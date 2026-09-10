# Shared fork history

Lets a group of hard-synced semi-persistent vectors share one branch history and
one restore token instead of each carrying its own. This is a **wall-clock and
memory** optimization aimed at the e-graph, which runs ~10 vectors in permanent
lockstep. It is a design doc; CI gates are the source of truth.

## Purpose

When `N` vectors always `mark` and `restore` together — at the same decision
levels, on the same branches, forever — their branch genealogies are *identical*
and their restore tokens agree on everything but `container_id`. Yet each vector
maintains its own `ForkHistory`, its own depth bookkeeping, and validates its
own token on every restore. That is `N` copies of one tree and `N` genealogy
walks per backjump. This removes the redundancy: one shared history, one token,
per-vector work only where the data actually differs.

The e-graph's hard-synced set: two union-find columns (`parent`, `rank`), the
three sparse-set vectors (`dense`, `sparse`, `indices`), the class ring, the
use-list arena's two vectors, the min-pool, and the per-kind node caches. All
mark/restore in lockstep with the decision level.

## Current representation and where the redundancy is

Each `Vec<T, I, S, TRACK>` owns:

- `diff_log: Vec<(T, I)>` — **per-vector** (different values). Not shareable.
- `frames: Vec<Frame<I>>` where `Frame = { saved_len, diff_start }` —
  **per-vector** contents (each vector's length and stratum differ), but the
  **stack depth is shared** (all synced vectors are at the same level).
- capture state (bits/counter) — **per-vector** (different cells).
- `forks: ForkHistory` + depth + token counters — **fully redundant**: identical
  across the group, because forks/restores happen in lockstep.

Composition today is struct-of-tokens: a container holding several vectors
hand-writes `mark`/`restore` that fan out to each field and bundles their tokens.
Correctness relies on the caller marking and restoring all fields together — the
"hard-sync" is a convention, not an enforced structure, and the `ForkHistory`
duplication is its cost.

`ForkHistory` is the sharpest waste: per the container docs it grows one
`origin` entry per restore and is never reclaimed, so its size scales with total
backtracks over the session — multiplied by `N`.

## Design: unbundle the history

Move `ForkHistory` + depth + token counters out of `Vec` into a standalone
`History`. `Vec` keeps only its own diff state. `mark`/`restore` take the history
by reference:

```
pub struct History { forks: ForkHistory, depth: usize, /* token counters */ }

pub struct GroupToken { branch_id: u32, depth: u32, frame_idx: usize }

impl History {
    pub fn mark(&mut self) -> GroupToken;          // one genealogy write, O(1)
    pub fn is_valid(&self, t: GroupToken) -> bool; // one validation
    pub fn restore_to(&mut self, t: GroupToken);   // pop genealogy once
}

impl<T, I, S, const TRACK: bool> Vec<T, I, S, TRACK> {
    // push local (saved_len, diff_start) frame; no genealogy work
    fn push_frame(&mut self, shrink: ShrinkPolicy);
    // reverse-replay + truncate this vector's diff to the token's frame
    fn restore_frame(&mut self, t: GroupToken);
}
```

`GroupToken` drops the per-vector `container_id`: one token names the whole
group's version. Validity and genealogy live in `History` and are checked once.

## Two modes, no aliasing, no const generic

Because `History` is a parameter, not a stored field, there is nothing to alias
— which keeps the whole thing inside Verus's reach.

- **Solo** — a thin wrapper bundling one `Vec` with one `History`, reproducing
  today's `mark()`/`restore(token)` API exactly. Existing call sites and the
  standalone vector semantics are preserved bit-for-bit; this is the migration
  safety net.
- **Synced group** — one `History`, many `Vec`s:

  ```
  fn mark(&mut self) -> GroupToken {
      let tok = self.history.mark();              // the only genealogy write
      for v in &mut self.members { v.push_frame(shrink); }
      tok
  }
  fn restore(&mut self, tok: GroupToken) {
      assert!(self.history.is_valid(tok));        // one validation
      for v in &mut self.members { v.restore_frame(tok); }
      self.history.restore_to(tok);
  }
  ```

Const-generic mode selection was rejected: the modes differ in method
*signature* (`mark()` vs a history-taking form), which a const generic cannot
switch. Unbundling gives both modes for free and avoids stored references.

## What it saves

- **Memory:** `ForkHistory` (unbounded-growth, never reclaimed) collapses from
  `×N` to `×1`. Depth/token counters likewise. For the e-graph's ~10 synced
  vectors, that is close to an order of magnitude on the *history* component.
- **Runtime:** per backjump, token validation and genealogy pop run **once**
  instead of `N` times; per `mark`, the fork bookkeeping runs once. The
  per-vector frame push and diff replay remain (`O(N)` small ops) — those are
  irreducible, since each vector really does have its own diff. So the win is
  concentrated on the redundant genealogy/validation work, which is exactly the
  part that scales with `N` and with backtrack frequency.

**Honest bound.** This does not touch the per-vector diff replay, the per-assert
`rebuild`, or the adapter's id indirection. Its share of the wall-clock gap is
whatever fraction the fork-history/validation work occupies — to be measured
(the differential profile) before committing the refactor, not assumed.

## Ownership model and verification

`History` is owned by the group (or by the solo wrapper) and passed to members
as `&mut` per call — never stored inside a member — so there is no shared
mutable aliasing for Verus to fight. Proof structure:

- **`History` invariants standalone:** genealogy well-formedness (the existing
  `ForkHistory` theorems, lifted to the extracted type).
- **Group invariant:** for every member, `member.frames.len() == history.depth`.
  This single cross-cutting fact ties the shared depth to each per-vector frame
  stack and is maintained by `mark` (push everywhere) and `restore` (pop
  everywhere).
- **Refinement theorem:** a synced group behaves exactly as `N` vectors each
  carrying an identical private `History` — i.e., sharing changes performance,
  not semantics. This lets the per-vector proofs be reused against the shared
  depth/token supplied by `History`.

## Migration path

1. Extract `History`; make `Vec` history-less with `push_frame`/`restore_frame`.
2. Add the `Solo` wrapper; port existing tests unchanged (green ⇒ semantics
   preserved).
3. Add `SyncGroup`; migrate the e-graph aggregates (`EClasses`, `NodeStore`) to
   hold one `History` and register their vectors as members, replacing the
   hand-written struct-of-tokens fan-out.
4. Benchmark: e-graph backtrack-heavy runs (eq_diamond family), reporting
   wall-clock and peak memory, solo vs synced.

## Interaction with other work

Independent of diff-stack compression (`09-diff-stack-compression.md`):
compression changes the *frame representation*, sharing changes *who owns the
history*. They compose — a `SyncGroup` of `COMPRESS = true` vectors is well
defined — but ship and measure them separately so each effect is attributable.

## Benchmark plan

Primary metric: wall-clock on the diamond-heavy e-graph benchmarks (the
backtrack-dominated case where genealogy work is hottest), solo vs synced.
Secondary: peak memory (the `ForkHistory ×N → ×1` collapse). Prerequisite: the
differential profile attributing the semper-vs-basic gap across
{fork-history/validation, per-vector mark/restore, per-assert rebuild, id
indirection}, so this refactor is pointed at a measured bottleneck rather than a
presumed one.

## Implementation plan (code-level)

Grounded in the code as it stands. `Vec<T, I, S, const TRACK: bool = true>`
(`vec.rs:640`) embeds `forks: ForkHistory` (`vec.rs:653`) and `id: ContainerId`.
`ForkHistory` (`fork_history.rs:34`) is `{ current_branch_id: u32, origins:
Vec<ForkOrigin> }` with `fh_wf` and the `fork_valid` walk. Token validity
(`is_token_valid_spec`, `vec.rs:701`) reads `self.forks.origins@`,
`self.forks.current_branch_id`, and `self.frames@.len()`; `wf` includes
`self.forks.wf()` (`vec.rs:851`); `mark`/`restore` ensures reference the fork
state throughout. Consumers that compose `Vec`s and today bundle their tokens:
`sparse_set.rs`, `circular_list.rs`, `list.rs`, `union_find.rs`, and the
`eclasses.rs` aggregate over all of them.

**This refactor is atomic, not incremental.** Extracting `ForkHistory` out of
`Vec` changes the signatures of `mark`/`restore` and the `wf` invariant, which
breaks every proof in the 3719-line `vec.rs` and every consumer at once. It
cannot land as a sequence of independently-verifying commits the way the
`matchable` bit or the compression encoder can. Plan it as one focused effort:

1. **Extract `History` (additive, verifies alone).** A standalone
   `History { forks: ForkHistory, depth: usize }` with the `ForkHistory`
   theorems lifted onto it (`fh_wf`, the `fork_valid` walk, headroom). `Vec` is
   untouched in this step; `History` just exists and verifies. This is the one
   safe increment and the right first commit.
2. **History-less `Vec`.** Remove `forks` from `Vec`; add `fn push_frame(&mut
   self, shrink)` (local `(saved_len, diff_start)` push, no genealogy) and `fn
   restore_frame(&mut self, tok: GroupToken)` (reverse-replay + truncate this
   vector to the token's frame). `mark`/`restore`/`is_token_valid_spec`/`wf`
   drop their fork clauses. Every ensures that named `self.forks.*` is rephrased
   against a supplied `&History`. `GroupToken { branch_id, depth, frame_idx }`
   drops `container_id`. This is the breaking change; it and step 3 land together.
3. **`Solo` and `SyncGroup` wrappers.** `Solo` bundles one `Vec` + one `History`
   and reproduces today's `mark()`/`restore(token)` bit-for-bit (the migration
   safety net: existing tests green ⇒ semantics preserved). `SyncGroup` owns one
   `History` and `N` members: `mark` = one `history.mark()` then `push_frame` on
   each member; `restore` = one `history.is_valid` then `restore_frame` on each
   member then `history.restore_to`. `History` is passed `&mut` per call, never
   stored in a member, so there is no shared mutable aliasing for Verus.
4. **Group invariant + refinement.** Prove `forall member: member.frames.len()
   == history.depth` (maintained by mark/restore fanning out), and the
   refinement theorem that a `SyncGroup` behaves as `N` vectors each carrying an
   identical private `History` — so the per-vector proofs are reused against the
   shared depth/token.
5. **Migrate aggregates.** `EClasses`/`NodeStore` and the composed
   `sparse_set`/`circular_list`/`list`/`union_find` hold one `History` and
   register their vectors as `SyncGroup` members, replacing the hand-written
   struct-of-tokens fan-out.

Because the wall-clock share was measured at 0.4% (the differential profile),
this is a memory optimization (`ForkHistory ×N → ×1`, unbounded-growth component)
and should be scheduled when memory is the target or as engine cleanup, not as a
speed fix.

## Size and savings estimate (which workload this is for)

`ForkOrigin` is 8 bytes (two `u32`), and `origins` grows by one per restore and is
never reclaimed (`vec.rs`: "origins.len() is the lifetime restore count"). Marks
do not add to it. So per vector `fork_history_heap ≈ 8 · R` bytes for `R` lifetime
restores, and with the e-graph's ~`N`=10 hard-synced vectors each holding an
identical `origins`, sharing collapses `×N → ×1`:

```
space saved ≈ 8 · R · (N − 1) ≈ 72 · R  bytes   (N = 10)
```

| R (restores) | ×N today | shared | saved |
|---|---|---|---|
| 10³ | 80 KB | 8 KB | 72 KB |
| 10⁴ | 800 KB | 80 KB | 720 KB |
| 10⁵ | 8 MB | 0.8 MB | 7.2 MB |
| 10⁶ | 80 MB | 8 MB | 72 MB |

**This is an SMT memory optimization, not an eq-sat one.** The cost scales with
restores: SMT (CDCL) backjumps constantly (`R` = 10⁴–10⁷ on hard problems), so its
fork history reaches tens of MB of 90%-redundant genealogy; equality saturation
leans on rewrites with little backtracking (`R` small), so its fork history is
negligible and compression is its memory lever instead. This corrects the earlier
framing that lumped both memory optimizations together.

**Time saving is negligible either way.** The per-restore genealogy work (an
`is_valid` parent-chain walk plus one `fork` push, done `N` times today vs once
shared) was measured at ~0.4% of eq_diamond wall-clock; sharing removes ~90% of
that, ~0.36%. Sharing is a memory optimization, not a speed one.

**Complementary, not covered by sharing:** sharing dedups `×N→×1`, but `origins`
still grows unboundedly with `R` in the one shared copy. Reclaiming it (below)
bounds the size to the live spine depth, which for SMT (large `R`, bounded depth)
is a larger space win than sharing and removes the unbounded-growth-per-session
problem. `R` per workload is measurable (count restores on a sundance SMT run vs
an eq-sat saturation) and should be measured before committing either change, per
the differential-profile prerequisite above.

## Reclamation COMPLETE across the whole fork API (2026-09-07)

The branch-model fork history is gone. `fork_history.rs` (the append-only
`origins` walk, `fork_valid`/`fork_walk`/`reaches`, `current_branch`) is deleted,
and every fork path uses `GenStamps`: the shared `History` (the e-graph's ×1 copy),
the standalone `Vec` and `AppendOnlyVec`, and the delegators that thread member
tokens (`circular_list`, `sparse_set`, `union_find`, `list`, `map`). `VecToken`
carries `(frame_idx, generation, container_id)`; validity is the O(1)
`forks.valid(frame_idx, generation)`; `mark` mints via `stamp_at`; `restore`'s
branch cut is `bump_from(frame_idx+1)`. Verifies containers-verus 1827/0, egraph
builds, and every test + conformance proptest passes. Live size is O(max depth)
on every fork path, not O(R): the leak is eliminated, not only for the e-graph.

**Measured, not only derived (`gen_stamps_reclamation`, containers-conformance).**
The AFTER is a runtime measurement: driving 500 and 50000 restore/re-mark cycles at
a spine depth of 1000 yields identical live size (`GenStamps::heap_bytes`), and the
array never grows past the deepened depth, so the size is independent of the restore
count. At depth 1000 the measured live size is 9 KB. The BEFORE is the deleted
`origins` model's known formula (8 bytes per restore, never reclaimed): at 10^7
restores it is 80 MB. Only the AFTER can be run (the branch model is deleted); the
test asserts the ratio is >=1000x (measured 9765x, MB to KB). This is a measurement
of the reclaimed structure, not an inference from an analogous case.

**`bump_from` is total (no overflow precondition), via `wrapping_add`.** The
invalidation a restore needs is only that a bumped level becomes *distinct* from a
stale token's stored generation, not that it increments: `x.wrapping_add(1) != x`
for every `u64` (the wrap `u64::MAX -> 0` still changes the value), so
`bump_from` invalidates the abandoned future with no precondition at all.
`lemma_bump_invalidates` is restated on `!=` rather than `+1`. `bump_from` is
`external_body` (trust group B: a pure counter bump, no `unsafe`) so the `!=`
ensures is read directly off `wrapping_add`'s semantics.

**Rejected alternative: thread a `< u64::MAX` headroom precondition.** The earlier
design carried `gen_headroom_spec` (a `forall d in (frame_idx, len): levels[d] <
u64::MAX`) as `restore`'s precondition, the u64 analogue of the old u32
`origins.len()+1 <= u32::MAX`. It fails to compose: `restore` is reached through
the delegators (`union_find` -> `parent.restore`, `circular_list` -> `entries.restore`,
`EClasses::restore` -> five members), and a `forall` over private `levels` cannot
be discharged O(1) at each boundary the way the old O(1) count check was. Threading
it produced a cascade of precondition failures across six files. `wrapping_add`
removes the obligation instead of propagating it. The only residue is ABA: a level
could wrap back to a stale token's generation after 2^64 restores at one depth,
which is physically unreachable, and frame-liveness (`frame_idx < depth`) backstops
it regardless. This is a decision, not a measurement: 2^64 is the bound, not an
observed value.

## Leak FIXED for the e-graph (2026-09-06)

`history::History` — the shared ×1 fork history the e-graph actually uses — is
migrated to `GenStamps` (containers-verus 1842/0, egraph + eclasses conformance
green). `GroupToken` now carries `(generation, depth)`; `valid_spec` is the O(1)
`stamps.valid(depth, gen)`; `mark` is `stamp_at(depth)`; `restore_to` is
`bump_from(t.depth+1)`, invalidating the abandoned future (tokens deeper than `t`)
while `t` and its ancestors stay valid — matching the branch model, sound by
`lemma_bump_invalidates`. The append-only `origins` is gone from this path.

**Memory (deterministic, from the structure).** Before: `origins` grew one 8-byte
`ForkOrigin` per restore, never reclaimed — `8·R` bytes for `R` lifetime restores.
After: `stamps.levels` is one `u64` per depth ever reached — `8·D_max` bytes for
max spine depth `D_max`. For an SMT run with `R = 10^7` backjumps at depth
`D_max ≈ 10^3`: **80 MB → 8 KB**, the MB→KB target. The O(R) term is eliminated
from the e-graph's fork history.

**Remaining:** (SUPERSEDED 2026-09-07 by "Reclamation COMPLETE" above: the
per-`Vec` migration is done and `fork_history.rs` is deleted.) the per-`Vec`
branch-model `ForkHistory` (used by the STANDALONE,
non-e-graph `Vec`/`AppendOnlyVec` fork API) still grows `origins` O(R). Migrating
it is coupled by the shared `VecToken` (both `Vec` and `AppendOnlyVec` use it), so
it is a separate atomic step (`VecToken.branch_id/depth -> gen`, `is_token_valid_spec`,
`mark`, the `restore` branch-cut proof, then delete `fork_walk`/`reaches`). Lower
priority: the e-graph (the memory-critical path) is now fixed; standalone `Vec`
fork usage is not the leak the goal targeted.

## Reclamation status: mechanism BUILT, integration is a scoped multi-step redesign

(SUPERSEDED 2026-09-07: integration is COMPLETE, see "Reclamation COMPLETE across
the whole fork API" above. The blast-radius estimate and stepwise plan below are
kept as the record of how the migration was scoped and executed.)

Labeling honestly (BUILT = verified code exists; DESIGNED = doc only):

- **BUILT:** `gen_stamps::GenStamps` — the depth-indexed stamp array with
  `stamp`/`push_level`/`bump_from`/`is_valid` and `lemma_bump_invalidates` (a
  diverging restore invalidates the abandoned future in O(1), preserves the
  spine). Verified 1841/0. This is the reclamation *mechanism*.
- **DESIGNED (not built):** wiring it in to actually bound live memory. Measured
  blast radius: 154 references to the branch-model validity surface
  (`VecToken.branch_id`/`depth`, `fork_valid`/`fork_walk`/`reaches`,
  `fork_count_spec`, `ForkHistory.origins`, `current_branch`) across 6 core files
  — `vec.rs`, `fork_history.rs`, `append_only_vec.rs` (a parallel fork impl),
  `history.rs` + `eclasses.rs` (the shared multi-member `History`), and the
  `fork_count_spec` delegators (`circular_list`/`sparse_set`/`union_find`/`list`).
  The fork token is a SHARED abstraction across every aggregate, so replacing the
  branch walk with the stamp array is not localized; it re-proves each container's
  restore/branch-cut against the new validity model. This is a multi-session
  redesign, not a single increment.

**Refinement (2026-09-06): `History` is the isolatable first target.** The
e-graph's shared ×1 fork history is `history::History` (with its own
`GroupToken { branch_id, depth }`), NOT the per-`Vec` `ForkHistory`: the members
mark/restore through `EClasses::{mark,restore}_with_history` over the genealogy-free
`push_frame`/`restore_frame`, so `History` is the sole fork authority for the
e-graph and the copy that leaks. Its `GroupToken` is separate from `VecToken`, and
its API is compact (`mark`/`is_valid`/`restore_to`, ~130 lines). So migrating
`History` to `GenStamps` fixes the e-graph leak in isolation — `GroupToken.branch_id
-> gen`, `valid_spec` = `stamps.valid(depth, gen)`, `mark` = `stamp_at(depth)`,
`restore_to` = `bump_from(t.depth)` with branch-cut safety from
`lemma_bump_invalidates` — without disturbing `VecToken`/`vec.rs`. The `Vec`/
`AppendOnlyVec` migration (coupled by the shared `VecToken`) is a separate later
step for the standalone (non-e-graph) fork API. Note: `GenStamps`'s `view()` spec
fn triggers Verus's opaque-field rule for cross-struct spec access; drop/rename it
and read `stamps.levels@` directly (as `Vec` reads `forks.origins@`).

**Stepwise integration plan (each a green increment):**
1. Add `GenForkHistory` (new type on `GenStamps`) additively, with `stamp_at(depth)
   -> gen`, `cut(depth)` (= `bump_from`), `is_valid(depth, gen)` — leaving the
   branch-model `ForkHistory` in place.
2. Pilot: migrate `AppendOnlyVec` (self-contained restore) to it — token carries
   `(frame_idx, gen)`, validity is `is_valid(frame_idx, gen)`, restore does
   `cut(frame_idx)`; re-prove its branch-cut safety via `lemma_bump_invalidates`.
   This proves the model end to end on a real container.
3. Migrate `Vec` (`VecToken.branch_id/depth` -> `gen`, `is_token_valid_spec`,
   `mark`, the `restore` branch-cut proof, `lemma_forks_change_preserves_wf`,
   Vec wf gains `stamps.len() >= frames.len()`).
4. Migrate the shared `History` + `EClasses`.
5. Delete the branch-model `ForkHistory`/`fork_walk`/`reaches` and the
   `fork_count_spec` u32-headroom preconditions (the leak-bounded design has no
   per-restore growth, so that headroom concern disappears).

Invalidation soundness at every step rests on `lemma_bump_invalidates`; the
per-container work is re-proving restore against `is_valid(depth, gen)` instead of
the walk. Memory goes O(R) -> O(max depth); measure SMT before/after at step 3.

## Reclamation core built (2026-09-06)

The dense stamp array below is now built and verified as a standalone module
(`gen_stamps::GenStamps`, containers-verus 1842/0): `levels: Vec<u64>` (one
generation per depth), `stamp(depth)` mints a token's generation, `bump_from(cut)`
invalidates the abandoned future by bumping `levels[cut..]`, and `is_valid(depth,
g)` is the single-read check `levels[depth] == g`. `lemma_bump_invalidates` proves
the soundness: after `bump_from(cut)`, every token at `depth >= cut` with its old
stamp is rejected while every token at `depth < cut` keeps its validity — exactly
what `fork_valid`'s parent-chain walk decides, now O(1) and O(max-depth) space
instead of O(R). Remaining: wire this into `ForkHistory` (replace the append-only
`origins` and the `fork_valid`/`reaches` walk with the stamp array, re-proving the
mark/restore/branch-cut theorems against it, preserving the ×1 sharing), then
measure the SMT memory before/after.

## Reclaiming abandoned branches (bounds size to O(spine depth))

`origins` grows one entry per restore and is never reclaimed because `branch_id`
is the entry's index in an append-only `Vec`: dropping an interior entry would
renumber the branch ids in tokens the client still holds. But most entries are
permanently dead, and the live ones are few.

**Every origin is already a guard.** `origins[b-1] = (parent_branch_id,
fork_depth)` states "on branch `parent_branch_id`, any mark deeper than
`fork_depth` is dead", and `fork_valid` already rejects a token by that comparison
(`token_depth <= origin.fork_depth` along the walk). So the rejection mechanism
exists; what is missing is discarding the guards no longer needed.

**What is permanently unreachable.** An entry matters only if its branch is on the
current branch's ancestor spine: the validity walk starts at `current_branch_id`
and climbs parent edges, and `fork` attaches every new branch to an ancestor of
current (`parent = token_branch <= current`). A branch off the spine is an
abandoned future whose tokens already fail `fork_valid`, and nothing created later
can reference it. Those entries are dead the moment the search diverges from them.

**Two reclamation rules.** On the backjump that cuts branch `p` at depth `d`:

- **Shallowest cut dominates.** If `p` is later cut at `d' < d`, the shallower
  guard rejects a superset, so keep only the minimum cut depth per branch and drop
  the rest.
- **Dead subtrees collapse.** Guards for branches strictly below a cut are
  subsumed by the guard at the cut, so drop the whole abandoned subtree and keep
  the single guard at its root.

The live guard set is then one shallowest cut per spine branch, so its size is
O(current spine depth), not O(total restores `R`).

**The rejection rule that makes dropping sound.** A token `(branch, depth)` is
valid iff `branch` is still live and `depth` is above every guard on its path. The
corollary that lets entries be dropped: a token whose `branch` is absent reads as
reject, "unknown branch is dead". That is sound only if branch ids are never
silently reused, so mint them from a monotonic counter, or recycle slots with a
generation tag that a stale token's old generation fails (defeating ABA: a
recycled id carrying the previous generation is rejected on the mismatch). Without
the tag a recycled id could wrongly accept a dead token.

**Dense alternative that also makes checking O(1).** Replace the parent-chain walk
with a depth-indexed generation array `gen: [u64]` of size the maximum depth,
reused across restores. A token carries `(depth, gen[depth])` at mark; a diverging
restore bumps `gen` for the levels it cuts; validity is the single read
`token.gen == gen[token.depth]`. This is the trail-solver level-stamp trick: it
bounds size to O(max depth) and turns validity from an O(spine depth) walk into an
O(1) array read, and `u64` generations do not realistically overflow. The sparse
guard set above and this dense stamp array are the same idea at different
densities; pick the stamp array when depth is small and dense, the guard set when
depth is large and sparsely cut.

**Arena allocation does not help the walk.** `origins` is already a single
contiguous `Vec<ForkOrigin>` (8-byte records), not a pointer-chased tree of
heap nodes, so there is nothing for an arena to flatten: the validity walk indexes
within one allocation already. The walk's cost is the number of parent hops (its
length is the spine depth) with a non-sequential index per hop, so the lever is
algorithmic, not allocational: shorten the chain by reclaiming (above), or remove
the walk entirely with the O(1) generation stamp. An arena would matter only if
the redesign moved to individually heap-allocated nodes, which it should not.

**The live spine is a stack, though `origins` is not.** `origins` as it stands
cannot be a LIFO pop-stack: it is indexed by restore-creation order, so an
abandoned branch is an interior entry, not the top, and the top entry is the live
branch you must keep. The genealogy is a tree, and a tree is not a stack. But the
*live* information is the current ancestor spine, and that is a stack: a
restore-to-ancestor pops the levels above the target, and a divergence pushes one.
Representing the spine explicitly as a depth-indexed level stack (the generation
array above is exactly this) gives pop-based reclamation and matches the
mark/restore discipline, where the shared `History.depth` already moves as a
stack. So the move is not "pop `origins`" but "store the spine stack instead of
the genealogy".

**The level index becomes a shared handle.** Once the spine is a dense
depth-indexed stack, a level's index is a compact `u32` key into parallel arrays,
the same dense-id-into-columns pattern the e-graph already uses. In the shared
design this is the natural join key: one shared level stack, and each synced
member's per-level frame addressed by the same level index, so the shared
`History` owns the level identity and each member owns only its frame column.
Reclaiming a level then reclaims everything keyed by its index in one step, a
clean ownership model. The caveat is the same generation tag as for tokens: if
level slots are recycled, an index alone is ambiguous (ABA), so a reference must
carry `(index, generation)` and a stale reference is rejected on the generation
mismatch. An index used purely within one non-recycled lifetime needs no tag.

Reclamation is a redesign of the validity mechanism (the token gains a generation
or the guard set replaces `origins`, and branch-id allocation changes), not a GC
pass bolted onto today's `origins`. It composes with sharing on the space axis and
supersedes it when `R` is large; the ~0.4% time share is unchanged either way,
except the generation-stamp form which also removes the walk.

### Reclamation savings estimate

Reclamation bounds the structure from O(total restores `R`) to O(live decision
depth `D`). For SMT, `R` is 10⁴–10⁷ but `D` (the CDCL decision-stack depth) stays
in the hundreds–low thousands, because backjumping keeps the stack shallow.
Per vector the fork history goes `8·R → 8·D` bytes; the whole e-graph, combined
with sharing, `8·N·R → 8·D`:

| `R`, `D` | ×N today (N=10) | reclaimed + shared | saved | factor |
|---|---|---|---|---|
| R=10⁴, D=10² | 800 KB | ~0.8 KB | ~800 KB | ~1000× |
| R=10⁵, D=10³ | 8 MB | ~8 KB | ~8 MB | ~1000× |
| R=10⁶, D=10³ | 80 MB | ~8 KB | ~80 MB | ~10000× |
| R=10⁷, D=10⁴ | 800 MB | ~80 KB | ~800 MB | ~10000× |

The reduction is ~`R/D` (100×–1000×) from reclamation times ~`N` (10×) from
sharing, but the qualitative point dominates: today the structure grows unbounded
with session length; reclamation makes it O(depth), so it **stops growing**. Once
it is a few KB, duplicating it ×N is trivial — so **reclamation largely obviates
sharing on the space axis**; do reclamation and you barely need sharing for memory.

CPU is a fraction of 0.4% either way (nil): the validity walk is already short (a
valid token validates against a recent ancestor, a few hops), so the O(1)
generation read removes a walk that was never the bottleneck, and reclamation's
per-backjump bookkeeping roughly offsets it. Wall-clock stays dominated by diff
replay and rebuild. Estimate, `D` unmeasured; measure decision depth on a real
SMT run to confirm.

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

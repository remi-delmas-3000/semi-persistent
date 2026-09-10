# Goal: ForkHistory Option C + layered frame compression

Task contract for the final build before the Sundance integration. Acceptance is a
runnable check per item, not a description. Every deliverable is labeled BUILT (the
artifact exists and its own check passes), MEASURED (a number about it exists), or
DESIGNED (a doc only). A goal that asks for BUILT is not discharged by MEASURED or
DESIGNED.

## One-line outcome

One `ForkHistory` owns N heterogeneous semi-persistent vectors and is the sole
authority for mark and restore, sequential and rayon-parallel; each frame is
compressed by a layered encoder chosen per frame from measured evidence, and restores
itself directly to the live column with a sliced memcpy where its indices are
contiguous.

## Starting state (established, verified green at HEAD)

- Phase A of the previous goal is complete: `None`, `ValueDict`, `IndexRuns`,
  `IndexRunsSorted` are integrated on the live `Vec` path, each with a differential
  restore==oracle test and a `tracking_bytes < plain` check.
- `CompressedFrame` / `HotFrame` traits exist: `decode`, `decode_at`, `entry_len`,
  `restore_to`, `add_write`, `compress(mode)`. `RunCol::restore_to` is the sliced
  memcpy; `DictFrame` / `Plain` / `HotFrame` restore scattered. All verified.
- `Vec::restore` does NOT call `restore_to`. It still runs the scattered overlay, so
  the memcpy path is verified but unused. This is the largest known performance gap.
- `history.rs` has `History` (GenStamps + depth), `Solo` (N=1) and `SyncPair` (N=2,
  one shared history, verified group invariant). Every `Vec` still carries its own
  `forks: GenStamps` and `id: ContainerId`, so a group supplements per-member state
  instead of replacing it. The e-graph does not use `history.rs` at all.
- Verus verifies `Box<dyn Trait>` with `spec fn`s and contracts, including a
  heterogeneous `Vec<Box<dyn Member>>` fanned out in a loop under a group invariant
  (probe run 2026-09-07; the negative control failed, so the probe is not vacuous).
  Dynamic dispatch is therefore available and no macro-generated group is needed.

Measured baseline, `scheme_comparison_bench`, N=10 000, ratio against plain. These
are ENCODED SIZES ONLY. No restore time is measured here, and no mode can be judged
on this table alone:

| shape | plain | idx-major write-order | idx-major sorted | val-major packed |
|-------|-------|-----------------------|------------------|------------------|
| union_find D=64 | 1.00x | 1.50x | 1.37x | **0.36x** |
| union_find D=4 | 1.00x | 1.50x | 1.37x | **0.30x** |
| contiguous | 1.00x | **0.51x** | **0.51x** | 0.95x |
| scattered_unique | 1.00x | 1.50x | 1.37x | 0.98x |

**Size is half the objective.** Index-major is the only family whose frames restore
by `copy_from_slice`, so its restore time is the other half, and that half is not yet
measurable: `Vec::restore` does not call `restore_to` (F1). A mode that encodes
larger than plain can still win by restoring several times faster, and the two axes
diverge by shape: the contiguous shape is 0.51x AND memcpy-restorable, while the
scattered shapes coalesce into thousands of one-entry runs where memcpy buys little.
No mode is kept or dropped on size alone. F1 lands before F5 precisely so the sweep
can measure both axes.

## Global invariants (checked at EVERY commit)

- `cargo verus verify -p semi-persistent-containers-verus` reports 0 errors. A commit
  with a failing proof is not made, ever.
- All semi-persistence and fork-reclamation theorems still hold: no theorem is
  weakened or deleted to make a new representation fit. Weakening a contract to a
  multiset contract is permitted only where the previous goal already established it.
- Findings, including negative ones, are recorded in the design docs with the number
  and the bench that regenerates it.

## Optimal-first clause

State the optimal choice before coding and use it. `Vec<Box<dyn SyncMember>>` is the
optimal group representation because the probe shows Verus verifies it and it is
N-flexible and rayon-friendly; a macro-generated fixed-arity group is a downgrade.
`restore_to` on the live restore path is the optimal restore because a contiguous
frame becomes one `copy_from_slice`; the scattered overlay is a downgrade. Any
downgrade is justified in one line and approved before it is coded.

## Hard-part-first ordering; no lateral motion

The pinned order is F1, then H1, then the rest. F1 and H1 break the most proofs and
carry the most unknowns. Do not start an adjacent or additive item while the current
one is incomplete. If blocked, stop and state the exact blocker.

===============================================================================
## Phase F: layered frame compression

### F1 (BUILT, PINNED FIRST): `Vec::restore` restores through `restore_to`

The reconstruction currently walks decoded pairs and overlays them one at a time.
Replace that with a per-frame `restore_to` call so a contiguous frame restores by
memcpy. The hot frame restores itself the same way (hot to live), with no
cold to hot to live detour.

- F1.1. `cargo verus verify` is green with `Vec::restore_frame` calling
  `CompressedFrame::restore_to` / `HotFrame::restore_to` and no residual pair-by-pair
  overlay loop on the restore path.
- F1.2. Every existing live-column differential test still passes unchanged:
  `value_major_compaction_tests`, `index_major_compaction_tests`,
  `index_major_sorted_compaction_tests`, `adaptive_compaction_tests`, plus
  `cargo test -p containers-conformance` in full.
- F1.3. MEASURED: a restore benchmark on a contiguous-capture column reports the
  memcpy path faster than the pre-change scattered path, with both numbers recorded.
  A projected speedup does not count.

### F2 (BUILT): the layered encoder, seven modes

An index layer and a value layer compose on one frame instead of excluding each
other. Index layer: none, write-order runs, sorted runs. Value layer: none, value
runs (RLE within an index run), value runs plus dictionary. The seven modes to
support are: `ValueDict`, `IndexRuns`, `IndexRuns+ValueRuns`,
`IndexRuns+ValueRuns+ValueDict`, `IndexRunsSorted`, `IndexRunsSorted+ValueRuns`,
`IndexRunsSorted+ValueRuns+ValueDict`.

- F2.1. `cargo verus verify` green with each mode a `CompressedFrame` impl proving
  `decode().to_multiset() == input.to_multiset()`, and the exact-sequence contract
  `decode() == input` for every non-sorting mode.
- F2.2. A conformance proptest (>= 1000 cases) round-trips every mode and asserts
  each restores a live column to the same contents as the reference application of
  the pairs.
- F2.3. MEASURED: `scheme_comparison_bench` extended to all seven modes on all four
  shapes, table recorded in doc 09.
- F2.4. Dictionary codes stay fixed-width bit-packed. Varint is rejected as a
  regression for dense small-`D` codes and the rejection is recorded with the number
  (2 bits per code at D=4 packed against 8 bits per code under byte-granular varint).

### F3 (BUILT): delta encoding, proved free of overflow and underflow

For columns where the old value is the cell's own index (a self-parented union-find
root) or near it, store `value - index`. The arithmetic must be proved in range, not
tested: `IndexLike` has no negative values, so the encoder stores a sign flag or uses
`checked_sub` in both directions, and the decoder reconstructs with `checked_add`.

- F3.1. `cargo verus verify` green with the delta encoder carrying
  `decode() == input` and NO `assume`, and with every add and subtract discharged by
  the verifier rather than guarded by an `external_body` wrapper.
- F3.2. A conformance proptest covers the boundary values: `value == index`,
  `value == 0`, `value == I::max()`, `index == 0`, `index == I::max()`, and random
  pairs, asserting exact round-trip.
- F3.3. MEASURED: bytes on a self-parented-root frame recorded against plain.

### F4 (BUILT): the shadow-encode harness

Encoders are pure functions of a frame, so every mode can be computed for every frame
without changing what the column stores. Add an exploratory mode that, at each
compact, encodes the frame in ALL modes and logs one record per (container, frame).

- F4.1. Each record carries: container name, frame index, entry count `N`, distinct
  value count `D`, write-order run count, sorted run count, value-run count, the byte
  size under every mode including plain, and the mode the live selector chose.
- F4.2. The harness is off by default and costs nothing when off (the compact path
  is unchanged unless the mode is enabled).
- F4.3. `cargo verus verify` stays green: the harness does not weaken any contract.

### F5 (MEASURED): per-column decision from real e-graph frames

Run the harness over real equality-saturation and SMT workloads and decide each
column from its own numbers.

- F5.1. A table per e-graph column (union-find parent, proof forest parent, node
  caches, sparse set `sparse` / `indices` / `dense`, class ring, use-list arena)
  giving `N`, `D`, run counts, and for every mode BOTH its encoded size against plain
  AND its measured restore time against plain. A size-only table does not satisfy
  this item.
- F5.2. Every hypothesis below is confirmed or refuted with its number, and refuted
  ones are recorded as negative results, not dropped:
  - dictionary wins on the union-find parent column because a class merge repoints
    every member from one shared old root, and because recanonicalization after a
    merge rewrites the same old value in many places while only stabilized states are
    captured;
  - dictionary is useless on the proof forest (each node points to a different node)
    and delta wins there instead;
  - node caches and the `dense` class-data column cannot use a dictionary at all
    because their values are structs, not `IndexLike`;
  - the class ring and the use-list see frames too small to amortize any header, so
    plain wins;
  - the use-list may still win with a dictionary when a frame first-touches many
    empty heads, because every captured old value is then the same sentinel.
- F5.3. Index-major is dropped only if it loses on BOTH axes on every real column:
  larger encoded size AND no restore-time advantage once memcpy restore is live
  (F1). Losing on size while winning on restore time keeps it, and the tradeoff is
  recorded per column so the choice is auditable. Dropping it before F1 makes the
  memcpy path measurable, or on size alone, is a forbidden proxy.

===============================================================================
## Phase H: ForkHistory Option C, the history owns the members

### H1 (BUILT, PINNED AFTER F1): `SyncMember` and the owning `ForkHistory`

`push_frame(shrink)`, `restore_frame(depth)` and the compact entries mention neither
`T` nor `I`, so a `SyncMember` trait is object-safe. The history holds
`Vec<Box<dyn SyncMember>>`, the generation stamps, the depth and the container
identity, and is the only type with `mark` and `restore`.

`SyncMember` exposes exactly three operations, all genealogy-free and all free of
`T` and `I` in their signatures:

- `seal_frame(mode)`: compress the member's open hot frame into a cold frame in the
  given per-frame mode, then open a fresh empty hot frame. This is the hot to cold
  translation, and it is per-member work with no cross-member dependency.
- `restore_frame(depth)`: reconstruct the member to its own snapshot at `depth` by
  applying its frames DIRECTLY to its live column through `CompressedFrame::restore_to`
  and `HotFrame::restore_to`. No intermediate pair vector is materialized: cold goes
  straight to live, and so does hot.
- `depth_spec()` / `wf()`: the spec-level state the group invariant quantifies over.

`ForkHistory::mark` writes ONE generation stamp and bumps ONE depth, then fans
`seal_frame(mode)` out over every member. `ForkHistory::restore(token)` validates the
token ONCE against the shared stamps, fans `restore_frame(token.depth)` out over
every member, then records the branch cut ONCE. The genealogy is touched only outside
the fan-out, which is what makes the fan-out parallelizable in H3.

- H1.1. `cargo verus verify` green with `SyncMember` carrying spec-level contracts
  and `ForkHistory::mark` / `restore` proving the group invariant: after `mark` every
  member's depth equals the history depth plus one and every member's view is
  unchanged; after `restore(t)` every member's depth equals `t.depth` and every
  member's view equals its own snapshot at `t.depth`.
- H1.2. `mark` seals a frame in every member: a test asserts each member's cold frame
  count grew by one and its hot frame is empty. A `mark` that only bumps depths fails
  this item.
- H1.3. `restore` applies frames straight to the live column: no call site on the
  restore path materializes a decoded pair vector. A restore that decodes to pairs and
  then overlays fails this item.
- H1.4. A test builds a group of at least three members of DIFFERENT `T`/`I`/`S` and
  drives interleaved mark and restore against per-member oracles.

### H2 (BUILT): `Vec` loses its own genealogy

Replace per-member state, do not supplement it.

- H2.1. `grep -n "forks\|id: ContainerId" containers-verus/src/vec.rs` shows the
  fields are gone from `struct Vec`. A `Vec` that still owns `GenStamps` fails this.
- H2.2. Standalone use is a `ForkHistory` with one member and keeps working: the
  existing standalone tests pass with at most a mechanical call-site change.
- H2.3. `cargo verus verify` green, token validation and the cross-container forgery
  rejection now living on the history.
- H2.4. MEASURED: peak bytes for a ten-member group under shared history against the
  same ten members each carrying their own history, both numbers recorded.

### H3 (BUILT): parallel compression on mark, parallel decompression on restore

What is parallelized is exactly the per-member fan-out, and nothing else:

- `mark_parallel`: the ONE stamp and depth bump happen first, sequentially. Then
  every member's `seal_frame(mode)` runs concurrently. This is parallel COMPRESSION:
  each member independently encodes its own hot frame.
- `restore_parallel`: the token is validated ONCE, sequentially. Then every member's
  `restore_frame(depth)` runs concurrently. This is parallel DECOMPRESSION straight
  into each member's live column, memcpy where the frame's indices are contiguous.
  The branch cut is recorded ONCE afterwards, sequentially.

Soundness of the fan-out: each member owns its own store, diff log and frame stack,
so the `&mut` borrows handed to the threads are disjoint, and no member reads another
member's state during the fan-out. The genealogy, the only shared mutable state, is
written strictly outside it. This disjointness is the justification recorded for the
`external_body` on the rayon call.

- H3.1. `mark_parallel` and `restore_parallel` exist with contracts IDENTICAL to
  their sequential counterparts, `external_body` over a rayon fan-out only.
- H3.2. The twins actually spawn: an instrumented run shows the fan-out executing on
  more than one thread. A twin that silently calls the sequential path fails this
  item.
- H3.3. A differential test drives the same workload through the sequential and the
  parallel path for BOTH mark and restore, asserting identical final contents,
  identical per-member depths, and identical per-member encoded sizes.
- H3.4. Threshold-gated on member count and per-member column work, with SEPARATE
  thresholds for mark and restore: compression and decompression have different cost
  profiles and their crossing points are measured independently.
- H3.5. MEASURED: wall-clock for sequential against parallel, reported separately for
  mark (compression) and restore (decompression), on a ten-member group, with each
  threshold chosen from its own measured crossing point. A single combined number
  does not satisfy this item.

### H4 (BUILT + MEASURED): the e-graph adopts it

- H4.1. The e-graph's synchronized members are held by one `ForkHistory`; its own
  mark and restore call the history.
- H4.2. The e-graph test suite passes unchanged.
- H4.3. MEASURED: peak fork bytes and saturation wall-clock before and after.

===============================================================================
## Named forbidden proxies

- A computed or projected size standing in for a real encoder's measured output.
- A `_parallel` twin that never spawns, or that spawns but is not differential-checked
  against the sequential path.
- A `mark` that bumps depths without sealing each member's hot frame, or a `restore`
  that decodes frames to a pair vector before writing the live column. Both defeat
  the point of the design and fail H1.2 and H1.3.
- One combined parallel speedup number standing in for the separate mark
  (compression) and restore (decompression) measurements.
- A `ForkHistory` that owns members while `Vec` still carries `forks` or
  `ContainerId`; that is supplement, not replace, and fails H2.
- `external_body` on any reconstruction theorem, on the delta arithmetic, or on
  `SyncMember`'s contracts. `external_body` is permitted only for the rayon fan-out
  and for raw-memory slice copies, each with a conformance check.
- A synthetic-shape bench reported as the per-column decision. F5 requires real
  e-graph frames.
- The shadow harness reported as the per-column decision without the table.
- `restore_to` existing but not being on the live restore path, reported as F1 done.
- Judging any mode, and index-major in particular, on encoded size alone. Size and
  restore time are both required, and restore time is only real after F1.
- Dropping index-major before F5 produces both axes.

## Partial states are failure states

"Foundation laid", "substrate built", "wired but not proven" and "verified but not on
the live path" are failures, not progress. Each open item is reported with the exact
remaining obligation and what closes it.

## Status format

Every progress report labels each item BUILT / MEASURED / DESIGNED from the evidence
rather than the intent, and shows the command output, test name or diff. "It should
pass" fails the audit.

===============================================================================
## Appendix: the interfaces

Signatures are the contract. Anything below that changes during the build is recorded
here with the reason.

### Value-type capability, and why there are two member impls

The dictionary layer calls `T::as_usize` to key its hash map, and the delta layer does
arithmetic on values, so both require `T: IndexLike`. The index layers (runs, sorted
runs) and plain move values verbatim and need only `T: Copy`. The e-graph mixes both
kinds of column in one synchronized set: the union-find parent column has `T` a node
id (`IndexLike`, full mode set), while the node caches and the class-data `dense`
column hold structs (`Copy` only, index layers and plain only).

One `impl` cannot cover both, and a silent dict-to-plain fallback is a forbidden
proxy. The resolution is two concrete member types implementing one object-safe
trait, which `dyn` then unifies:

```rust
// Full mode set: plain, index runs (write-order and sorted), value runs,
// dictionary, delta.
impl<T, I, S, const TRACK: bool> SyncMember for Vec<T, I, S, TRACK>
where T: IndexLike + Default, I: IndexLike, S: DiffStore<T, I, TRACK> { .. }

// Opaque values (structs): plain, index runs, sorted index runs, value runs.
// No dictionary, no delta. A newtype so the two impls do not overlap.
pub struct OpaqueVec<T, I, S, const TRACK: bool>(Vec<T, I, S, TRACK>);

impl<T, I, S, const TRACK: bool> SyncMember for OpaqueVec<T, I, S, TRACK>
where T: Sized + Copy + Default, I: IndexLike, S: DiffStore<T, I, TRACK> { .. }
```

`ColdFrame` splits its constructor along the same line:

```rust
impl<T: Copy, I: IndexLike> ColdFrame<T, I> {
    // Plain / IndexRuns / IndexRunsSorted / +ValueRuns. Values move verbatim.
    pub fn compress_mode_copy(diffs: &Vec<(T, I)>, mode: CompressionMode)
        -> (r: ColdFrame<T, I>)
        requires mode.is_value_opaque(),
        ensures r.wf(), r.decode().to_multiset() == diffs@.to_multiset();
}

impl<T: IndexLike, I: IndexLike> ColdFrame<T, I> {
    // The above plus ValueDict and Delta.
    pub fn compress_mode(diffs: &Vec<(T, I)>, mode: CompressionMode)
        -> (r: ColdFrame<T, I>)
        ensures r.wf(), r.decode().to_multiset() == diffs@.to_multiset(),
                unique_idx(diffs@) ==> unique_idx(r.decode());
}
```

`CompressionMode::is_value_opaque()` is the spec-level predicate naming the modes that
need no `IndexLike` on `T`. Calling `compress_mode_copy` with a dict or delta mode is
a precondition violation, not a runtime fallback.

### The layered mode

```rust
pub struct CompressionMode {
    pub index: IndexLayer,   // None | Runs | RunsSorted
    pub value: ValueLayer,   // None | ValueRuns | ValueRunsDict | Dict | Delta
}
```

The seven modes to compare are the inhabited combinations named in F2, plus `Delta`
from F3 and `None/None` (plain) as the baseline. `IndexLayer::RunsSorted` is the only
layer that reorders, so it is the only one whose contract is the write multiset
rather than the exact sequence.

### `CompressedFrame` and `HotFrame` (BUILT, unchanged by this goal)

```rust
pub trait CompressedFrame<T: Copy, I: IndexLike>: Sized {
    spec fn wf(&self) -> bool;
    spec fn decode(&self) -> Seq<(T, I)>;

    fn entry_len(&self) -> (n: usize)
        requires self.wf(), ensures n == self.decode().len();

    fn decode_at(&self, i: usize) -> (e: (T, I))
        requires self.wf(), i < self.decode().len(),
        ensures e == self.decode()[i as int];

    fn restore_to(&self, target: &mut Vec<T>)
        requires self.wf(),
        ensures final(target)@ == apply_all::<T, I>(old(target)@, self.decode());
}
```

Impls: `DictFrame<T, I>`, `RunCol<T, I>`, `ColdFrame<T, I>`, and the layered frames
added by F2 and F3. `RunCol::restore_to` is the sliced `copy_from_slice`; the others
write scattered. `HotFrame<T, I>` carries `new`, `add_write`, `entry_len`,
`restore_to` with the same `apply_all` contract, and `compress(mode)`.

### `SyncMember`: object-safe, no `T` or `I`

Object safety is what makes `Box<dyn SyncMember>` legal, so no method mentions `T` or
`I`, no method is generic, and there are no associated types. The value type is
erased; only the spec-level view the group invariant needs survives.

```rust
pub trait SyncMember {
    /// Frame-stack depth. The group invariant quantifies over this.
    spec fn depth_spec(&self) -> nat;
    spec fn wf(&self) -> bool;

    /// Compress the open hot frame into a cold frame in `mode`, then open a fresh
    /// empty hot frame. Per-member work, no cross-member dependency: this is what
    /// the parallel mark fans out.
    fn seal_frame(&mut self, mode: CompressionMode, shrink: ShrinkPolicy)
        requires old(self).wf(),
        ensures final(self).wf(),
                final(self).depth_spec() == old(self).depth_spec() + 1;

    /// Reconstruct to this member's own snapshot at `depth`, applying frames
    /// DIRECTLY to the live column through `restore_to`. No decoded pair vector is
    /// materialized. This is what the parallel restore fans out.
    fn restore_frame(&mut self, depth: usize)
        requires old(self).wf(), depth < old(self).depth_spec(),
        ensures final(self).wf(), final(self).depth_spec() == depth as nat;

    /// Diagnostic footprint, for the H2.4 peak-bytes measurement.
    fn heap_bytes(&self) -> usize;
}
```

`T: Default` is required by the reconstruction (it regrows a popped region with
default fillers), so it sits on the impls, not on the trait.

The per-member snapshot equality that `ForkHistory::restore` must prove cannot be
stated over an erased `T`. It is carried as a per-member spec sequence:
`spec fn view_hash(&self) -> Seq<nat>` is rejected as lossy. Instead `SyncMember`
declares `spec fn snapshot_at(&self, k: nat) -> bool` meaning "the live column equals
this member's own snapshot at depth `k`", proved by each impl against its concrete
`view()`. `restore_frame`'s ensures gains `final(self).snapshot_at(depth as nat)`.

### `ForkHistory` and its token

```rust
pub struct GroupToken {
    pub depth: u32,
    pub generation: u64,
    pub group_id: ContainerId,
}

pub struct ForkHistory {
    members: Vec<Box<dyn SyncMember>>,
    stamps: GenStamps,   // depth-indexed generations, branch-cut safety
    depth: usize,
    id: ContainerId,     // cross-group forgery rejection, one per group
}

impl ForkHistory {
    pub open spec fn wf(&self) -> bool {
        &&& self.stamps.wf()
        &&& forall|k: int| 0 <= k < self.members@.len()
                ==> (#[trigger] self.members@[k]).wf()
        &&& forall|k: int| 0 <= k < self.members@.len()
                ==> (#[trigger] self.members@[k]).depth_spec() == self.depth as nat
    }

    pub fn add_member(&mut self, m: Box<dyn SyncMember>)
        requires old(self).wf(), m.wf(), m.depth_spec() == old(self).depth as nat;

    pub fn mark(&mut self, mode: CompressionMode, shrink: ShrinkPolicy) -> (t: GroupToken)
        requires old(self).wf(),
        ensures final(self).wf(),
                final(self).depth_spec() == old(self).depth_spec() + 1,
                t.depth == old(self).depth_spec();

    pub fn restore(&mut self, t: GroupToken)
        requires old(self).wf(), old(self).valid_spec(t),
                 (t.depth as nat) < old(self).depth_spec(),
        ensures final(self).wf(),
                final(self).depth_spec() == t.depth as nat,
                forall|k: int| 0 <= k < final(self).members@.len()
                    ==> (#[trigger] final(self).members@[k]).snapshot_at(t.depth as nat);

    // Identical contracts, rayon fan-out, threshold-gated. external_body.
    pub fn mark_parallel(&mut self, mode: CompressionMode, shrink: ShrinkPolicy) -> GroupToken;
    pub fn restore_parallel(&mut self, t: GroupToken);
}
```

Standalone use is `ForkHistory` with one member, so there is no second mechanism to
maintain.

### Open interface question to settle in H1

`mark` currently takes one `CompressionMode` for the whole group. Per-column
selection (F5) wants a mode per member, and per-frame selection (A4) wants it chosen
from the frame's own statistics. The likely resolution is that `seal_frame` takes no
mode at all and each member holds its own policy, choosing per frame from its own
statistics. That is settled in H1 with the signature recorded here before coding.

# Semi-Persistence Proof Roadmap

This file is the operational TODO for restoring the main semi-persistence
theorems across the three-tier Vec runtime and every derived container.

The current execution order follows
[`all-tier-semi-persistence-goal.md`](containers-verus/doc/tasks/all-tier-semi-persistence-goal.md),
the user-supplied continuation after H4: establish a shared physical frame
meaning, prove replay and all-tier composition, prove conversions and survivor
preservation, then reverify the derived public and parallel paths. H4 is the
verified Hot-only foundation; all-tier closure remains the goal.

The stable abstraction boundary MUST remain unchanged:

```text
mark:
    view/model unchanged
    depth_after == depth_before + 1
    snapshots_after == snapshots_before.push(old_view_or_model)

restore(k):
    view/model_after == snapshots_before[k]
    depth_after == k
    snapshots_after == snapshots_before[..k]
    surviving older frames remain valid
```

See [`containers-verus/doc/design/17-three-tier-frame-grid.md`](containers-verus/doc/design/17-three-tier-frame-grid.md)
for the geometric proof model and
[`containers-verus/doc/tasks/nightshift-semi-persistence-all-containers-goal.md`](containers-verus/doc/tasks/nightshift-semi-persistence-all-containers-goal.md)
for the full milestone protocol.

## Current verified checkpoints

| milestone | commit | result |
|---|---|---|
| H0: physical Hot proof cores | `df10134` | capture, set, mark, zero/nonzero restore cores |
| H1: pool-native general invariant | `706a305` | full Vec module green; `diff_log` no longer physical authority |
| H2a: Hot push/regrowth core | `8a3745b` | geometric grow-layer proof and checked re-entry |
| H2: Hot mutators | `5a5a6d4` | public `push`, `pop`, `set_index` checked through Hot-scope dispatch |
| H3: explicit Hot Defer marks | `d14ba85` | `Never` and thresholded shrink checked through `try_mark_with` |
| H4: public Hot restore | this checkpoint | general `wf`, surviving canonical prefix, Inline/Parallel restore; 2232 package facts verified |

At H3:

```text
Vec module:          140 verified, 0 errors
runtime regressions: 30 passed, 0 failed
trust surface:       85 default external_body markers + 5 literal-types markers
```

## Non-negotiable proof rules

- Every Trail, Hot, and Cold frame owns its own `saved_len`.
- Adjacent saved lengths are not monotone; restore may grow or shrink relative
  to any neighboring frame.
- For every `j < saved_len(f)`, frame `f` must either physically cover `j` or
  prove `j < layer_above(f).len` and inherit the snapshot value from that layer.
- `hot_value_pool`, `trail_value_pool`, and Cold runs are physical authority.
  Compatibility `diff_log` is inert and MUST NOT justify capture, extents, or
  reconstruction.
- Hot and Cold payload counts are bounded by a frame's `saved_len`; an
  undeduplicated Trail frame is not bounded because duplicate writes stack
  vertically.
- Persistent Hot frames are unique but unordered. Sorting is a transient local
  step inside Hot-to-Cold translation only.
- Do not add `admit`, `assume`, `assume_specification`, or a contract-bearing
  `external_body` to hide an obligation.
- Do not weaken public contracts or modify `containers/`, which remains the
  differential oracle.

## Critical path

```text
shared physical frame contract
→ Trail replay
→ Trail-to-Hot dedup refinement
→ Hot-to-Cold sort/run refinement
→ mixed-tier restore
→ configured/forced/adaptive policies
→ downstream public/parallel contract audit
→ final all-container verification
```

## 1. Hot restore — H4 complete

The H4 checkpoint strengthens zero/nonzero Hot restore to preserve
general `wf`, retains the canonical history prefix for surviving frames, and
checks the public Hot restore path for both Inline fused clearing and Parallel
pre-clearing. The existing trusted restore body is restricted to the exact
complement of `hot_defer_scope()`.

Completed local checks:

```text
restore-family query: 14 verified, 0 errors
InlineStore:          29 verified, 0 errors
ParallelStore:        29 verified, 0 errors
TrailStore:           27 verified, 0 errors
DynStore:             26 verified, 0 errors
runtime regressions:  30 passed, 0 failed
feature tests:        passed
policy matrix:        4 passed, PROPTEST_CASES=1024
trust surface:        84 default external_body markers + 5 literal-types markers
```

Fresh full-package verification passed: **2232 verified, 0 errors**.
The first package command reused a cached build and was not counted; the
fresh invocation touched `src/vec.rs` and used `--time-expanded`. See
`containers-verus/doc/tasks/three-tier-proof-progress.md` for exact results.
The obligations below are established for the all-Hot path. Mixed-tier
fallbacks remain trusted and belong to later milestones.

### 1.1 Zero target

Prove:

```text
view_after       == old snapshots[0]
depth_after      == 0
snapshots_after  == []
hot_stack        == []
hot_value_pool   == []
trail_frames     == []
full_trail       == []
capture flags    == clear
```

Sketch:

1. Resize to frame zero's own `saved_len`.
2. Prove every set flag is named by the Hot replay suffix.
3. Use protocol-specific clear:
   - Parallel/Dyn-Parallel call `begin_restore` to clear the bitmap.
   - Inline/Dyn-Inline clear tags during fused `restore_overlay` replay.
4. Replay the whole Hot pool and apply the Hot overlay telescope.
5. Clear physical and canonical frame stacks.
6. Clear inert compatibility `diff_log` at zero depth.
7. Prove `wf_for_snap` vacuously and reassemble general `wf`.

### 1.2 Nonzero target

For `target = k > 0`:

```text
physical_cut   = old hot_stack[k].start
canonical_cut  = old trail_frames[k]

view_after       = old snapshots[k]
hot_stack_after  = old hot_stack[..k]
hot_pool_after   = old hot_pool[..physical_cut]
trail_frames      = old trail_frames[..k]
full_trail        = old full_trail[..canonical_cut]
snapshots_after   = old snapshots[..k]
depth_after       = k
```

Sketch:

1. Resize to frame `k`'s own `saved_len`.
2. Replay `hot_value_pool[physical_cut..]`.
3. Prove the replay equals `old snapshots[k]`.
4. Truncate physical and canonical histories to their respective boundaries.
5. Reopen old frame `k - 1` as the surviving top.
6. Its new layer is `old snapshots[k]`, exactly its old layer; transfer its
   reconstruction locally.
7. Rebuild capture flags from the surviving Hot slice.
8. Pass the present restored length to `finish_restore`, not the survivor's
   saved length.
9. Reassemble canonical `wf_for_snap`, physical `hot_defer_wf`, and general
   `wf`.

Capture equivalence is required only when both:

```text
j < survivor.saved_len
j < restored_view.len
```

Saved columns above the restored live row remain physically covered.

### 1.3 Public Hot restore path

- Extract the mixed-tier body into `runtime_restore_frame_fallback`.
- Give it the exact precondition `!old(self).hot_defer_scope()`.
- Make `runtime_restore_frame` checked using `hot_defer_scope_exec()`.
- Remove the all-Hot path's `restore_frame` marker.
- Verify `restore_frame`, `restore`, and `try_restore` in that order.

Completion theorem:

```text
successful try_restore(token k):
    view_after == snapshots_before[k]
    depth_after == k
    snapshots_after == snapshots_before[..k]
```

## 2. Reverify every derived container — after all-tier Vec closure

Once the exact Vec theorem is checked through the public path, rerun existing
composition proofs without redesigning them unless verification exposes an
abstraction leak.

- **SparseSet:** three-column lockstep restore, permutation/inverse invariant,
  and common archived frame.
- **CircularList:** vector restore plus ring partition/cyclicity archive.
- **ListArena:** heads/nodes lockstep plus list-model archive.
- **UnionFind:** parent/rank and optional proof columns plus roots/dist archive.
- **BPlusTreeSet:** arena restore plus root/header/tree archive.
- **EClasses:** all nested containers, common-frame protection, and W1-W7
  aggregate archive.
- **SpMap/AppendOnlyVec:** independent prefix/truncation theorem and rebuilt
  hash index.

Expected proof composition:

```text
reproved unchanged Vec theorem
             ↓
existing component archive/refinement proof
             ↓
restored collection model
```

Classify any downstream failure before editing:

1. accidental unfolding of Vec physical internals;
2. dependency on an old trusted Vec wrapper;
3. independent collection invariant defect.

## 3. Prove Trail frames

Trail records every old value chronologically, including duplicates. For each
`(frame,index)` column, the oldest event is the mark-time value. Reverse replay
applies newest to oldest and therefore leaves the oldest value last.

Required proofs:

- every Trail entry index is below that frame's `saved_len`;
- the first chronological hitter stores the snapshot value;
- later duplicates preserve the first hitter;
- reverse replay reconstructs the snapshot;
- Trail marks preserve empty delimiters and arbitrary saved lengths;
- Trail pop/set append canonical and physical chronological events in lockstep;
- Trail restore rebuilds open ingress state exactly.

Do not assert a Trail payload-count bound before deduplication.

## 4. Prove Trail-to-Hot deduplication

For every Trail frame and index column:

```text
Trail: A, B, C
Hot:   A
```

Prove that `dedupe_first`:

1. retains every touched index;
2. retains the oldest value for that index;
3. produces unique indices;
4. preserves reverse-replay/frame reconstruction;
5. preserves frame order, empty delimiters, and per-frame `saved_len`;
6. leaves the ghost snapshot stack unchanged;
7. establishes `hot_entry_count <= saved_len`.

## 5. Prove Hot-to-Cold conversion

Persistent Hot is unique and unordered:

```text
unordered unique Hot
        ↓ transient in-place sort
sorted unique intermediate
        ↓ run formation
Cold disjoint runs
```

Prove:

- sorting is a permutation;
- permutation preserves uniqueness, count, index→value map, and reconstruction;
- sortedness is local to translation and not part of `hot_repr_ok`;
- run formation yields ordered, in-bounds, pairwise-disjoint runs;
- decoding runs returns the same Hot map;
- `cold_value_count <= saved_len`;
- `cold_run_count <= cold_value_count`;
- empty frame identity and `saved_len` survive conversion.

## 6. Prove Cold replay

For each saved cell:

```text
covered:
    cold_value == snapshot value

uncovered:
    index < layer_above.len
    layer_above[index] == snapshot value
```

Show direct run copies are equivalent to applying the unique frame map. When
`saved_len > layer_above.len`, every extra saved column must be covered by a
Cold run.

## 7. Prove mixed-tier restore

Logical age order is:

```text
oldest                           newest
Cold frames | Hot frames | Trail frames
```

To restore target `k`:

1. replay newer Trail frames in reverse chronological order;
2. apply newer Hot unique entries;
3. copy newer Cold runs;
4. apply the target frame;
5. resize to the target frame's own `saved_len`;
6. truncate all physical stacks and canonical ghost stacks;
7. promote/reopen the surviving top in the active DiffStore protocol;
8. rebuild capture state exactly.

Factor one policy-independent abstraction:

```text
decode(Trail frame)
  == decode(Hot frame)
  == decode(Cold frame)
  == canonical frame abstraction
```

## 8. Prove every rollover policy

### `Defer`

No tier conversion at mark. Hot Defer is nearly complete; Trail Defer remains.

### `ApplyConfigured`

Prove configured oldest-prefix migration changes only representation:

```text
Trail → Hot → Cold
```

Snapshots, depth, token coordinates, and restoration results remain unchanged.

### `ForceClosed`

Prove Trail→Hot and Hot→Cold independently and together, always in that order.

### Adaptive

Do not prove policy optimality. Prove that any selected closed prefix preserves
logical frames, never migrates the writable newest frame, and leaves the ghost
snapshot stack unchanged.

## 9. Reusable geometric lemma families

### Horizontal movement

- grow live row while preserving prefix;
- shrink live row after covering removed saved columns;
- capture departing saved column;
- restore exact target length.

### Vertical movement

- append an empty frame delimiter;
- preserve older-frame locality;
- truncate to a frame prefix;
- reopen the surviving top.

### One index column

- first physical capture;
- chronological duplicate append;
- oldest Trail event remains authoritative;
- capture-bit/range equivalence.

### Representation changes

- Trail dedup preserves the column map;
- transient Hot sort preserves the column map;
- Cold run formation preserves the column map.

### Whole stack

- `cold_count + hot_count + trail_count == snapshot_depth`;
- each segment maps its frame-local `saved_len` to the corresponding snapshot;
- restore consumes the target frame and preserves exactly the older prefix.

## 10. Validation and commit protocol

For function-scoped Vec queries:

```bash
cd containers-verus
touch src/vec.rs
cargo verus verify -- --verify-only-module vec --verify-function FUNCTION
```

At each milestone:

```bash
cargo fmt --all -- --check
cargo verus verify -p semi-persistent-containers-verus
cargo test -p semi-persistent-containers-verus --test three_tier_runtime
cargo test -p semi-persistent-containers-verus --features "compat-all,literal-types"
PROPTEST_CASES=1024 cargo test -p containers-conformance --release --test three_tier_policy_matrix
```

A reduced verified count caused by a new trusted body is failure. Update the
trust ledger and CI marker count whenever a marker is removed or added. Commit
every independently green milestone; do not commit the current H4 source edits
until their targeted and full gates pass.

## Definition of done

- The real public Vec path proves the unchanged snapshot-stack theorem for every
  supported three-tier policy.
- Arbitrary per-frame saved-length growth and shrinkage are covered.
- Trail, Hot, Cold, and every conversion refine the same frame abstraction.
- All derived collection persistence theorems verify against the real Vec path.
- No selected path is hidden behind a contract-bearing trusted wrapper.
- Full Verus, feature, runtime, differential, and consumer gates are green.
- Trust counts, proof progress, and design documentation match source.

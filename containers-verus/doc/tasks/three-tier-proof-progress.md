# Three-tier Vec proof progress

## 2026-09-14 — Milestone 1: unique Hot-only Defer

**Result: verified executable prefix.** Starting from clean `d21-exec` HEAD
`44b8657498f004c611bdda9d886a5621165ee0f2` (`origin/main` pinned at
`56a06a5adb450ad41b54ad14b7f66dd0b24a4201`), this milestone proves the
unique-capture, Hot-only state while rollover is deferred. No commit was
created.

### Authoritative projection

`Vec::hot_defer_wf` is a closed named predicate. `Vec::hot_defer_end` gives a
closed frame its header `end` and gives the writable top the effective end
`hot_value_pool.len()`. The projection reads `hot_value_pool` and `hot_stack`,
not `diff_log`, and states:

- `TRACK`, store well-formedness, and unique-capture ingress;
- empty Trail and Cold stacks/pools;
- `hot_stack.len == trail_frames.len == snapshots.len`;
- empty-history pool/ghost/cache/flag clauses;
- first start at zero, bounded header extents, and exact adjacency of closed
  header ends to the next start;
- `saved_len`/snapshot alignment and top `active_saved_len` alignment;
- `stratum_unique` for every Hot frame;
- `frame_inv_range` reconstruction for every Hot frame over its real pool
  extent;
- exact open-top capture bridge and no stray capture flags.

The temporary retained ghost boundaries are all zero and `full_trail` is empty
inside this projection. They provide logical frame coordinates only; physical
correctness is entirely pool-native.

### Verified proof and executable functions

Every query ran from `containers-verus` with `touch src/vec.rs` immediately
before `cargo verus verify -- --verify-only-module vec --verify-function NAME`.
The final batch exited zero; every item reported `1 verified, 0 errors`:

| function | role |
|---|---|
| `lemma_frame_inv_range_capture_append` | first-capture append preserves physical reconstruction |
| `lemma_frame_inv_range_set_captured` | a write at a captured top cell preserves reconstruction |
| `lemma_frame_inv_range_set_outside` | a write beyond saved extent is local to the live view |
| `lemma_hot_defer_start_monotone` | closed extent adjacency implies start monotonicity |
| `lemma_hot_defer_cell_eq_overlay` | pool-native frame-by-frame restore telescope |
| `hot_defer_capture_checked` | first unique capture appends once; duplicate capture is a no-op |
| `hot_defer_set_checked` | checked capture followed by raw set |
| `hot_defer_mark_checked` | seal prior header and open an empty Defer frame |
| `hot_defer_restore_zero_checked` | replay all Hot frames and retire history |
| `hot_defer_restore_nonzero_checked` | replay target suffix and rebuild surviving top flags |

The actual runtime branches call these cores. `runtime_capture` and
`runtime_set` select the checked unique cores; `runtime_push_frame` selects the
checked core for `Defer + ShrinkPolicy::Never`; and `runtime_restore_frame`
selects the checked zero/nonzero cores when non-fused unique history is entirely
Hot (Parallel protocol). InlineStore remains on its existing fused replay path,
where replay itself clears tags, avoiding a proof-induced second scan. External
dispatch wrappers are not counted as verified functions.

### Runtime validation

- `cargo test --test three_tier_runtime`: **30 passed, 0 failed**.
- `cargo test --test trail_vec`: **5 passed, 0 failed**.
- Added `unique_defer_restores_surviving_prefix_and_zero`, covering Inline and
  Parallel, repeated unique capture, pop/regrow with nonmonotone saved lengths,
  four explicit Defer marks including an empty frame, three surviving-prefix
  restores, target-zero restore, and final physical-stack emptiness.
- `cargo fmt --check`: initially identified only formatting in the new test;
  `cargo fmt` corrected it.

### Trust and parsing delta

The first attempted Vec query failed before verification because the locked
execution branch used policy datatypes declared outside `verus!` and planner
helpers containing unsupported std iterator/sort/arithmetic calls. The
resolution preserves runtime code:

- transparent external type registrations for `RolloverPolicy`, `TierLimit`,
  `ReclaimPolicy`, `TierPolicy`, `TierStats`, `AdaptiveInput`, and
  `AdaptiveReport`;
- one opaque registration marker for private-field `Ratio`;
- proof-erasure markers on `retained_closed_prefix` and
  `hot_frame_run_count`, whose std planner operations are unsupported.

This is **three new `external_body` markers** relative to `44b8657`: one opaque
type and two execution-only planner functions. `Vec::with_store_mode` and
`Vec::with_store_policy` now verify, including the empty unique-state
`hot_defer_wf` postcondition, so the pre-existing `with_store_policy` marker is
removed. Net source counts are 96 default and 101 with `literal-types`; axiom
counts remain 1 and 6. The checked milestone contains no `external_body`,
`admit`, or `assume`.

### Remaining work / first boundary

There is no failing obligation inside the stated Hot-only milestone: both zero
and nonzero Hot restore closed. The first unproved boundary is the transition
from general `Vec::wf` to `hot_defer_wf`: general `wf` still describes the inert
`diff_log` shadow and mixed Trail/Hot/Cold ownership. Consequently these remain
outside this milestone:

1. `runtime_push` and `runtime_pop`, including marked pop/re-entry;
2. shrink-enabled Defer marks;
3. ApplyConfigured and ForceClosed Trail-to-Hot/Hot-to-Cold conversion;
4. survivor promotion from Cold or Hot into Trail ingress;
5. mixed-tier restore and removal of the outer runtime/wrapper markers;
6. verified construction of `hot_defer_wf` from the public general invariant.

The next milestone should prove the protocol-specific partition/refinement
predicate that selects Hot-only Defer from general state, then discharge
push/pop or the first migration edge without reintroducing `diff_log` as a
physical authority.


## 2026-09-14 — Milestone H1: pool-native general invariant bridge

**Result: H1 fully verified, including the full Vec-module gate.** Work started
from clean H0 commit `df101348d1617f2ebe8c963b50f7f95a642fbd77` with
`origin/main` pinned at
`56a06a5adb450ad41b54ad14b7f66dd0b24a4201`. `containers/` was not changed.

### General invariant replacement

General `Vec::wf` no longer grants physical authority to inert `diff_log`. It
now composes these closed named predicates:

- `frame_partition_ok`: exact Cold + Hot + Trail header count against snapshots
  and ghost frame coordinates, plus saved-length mapping for all three age
  segments; zero-length extents retain their headers/token identity;
- `hot_repr_ok`: Hot header bounds/adjacency, pool-length effective newest end,
  per-frame uniqueness, and reconstruction over `hot_value_pool`;
- `trail_repr_ok`: Trail header bounds/adjacency, pool-length effective newest
  end, and the named chronological reconstruction boundary over
  `trail_value_pool`;
- `cold_repr_ok`: the pre-existing run/value pool partition, empty-pool facts,
  run disjointness, and named Cold reconstruction boundary;
- `open_ingress_ok`: `DiffStore::unique_capture_spec()` selects Hot versus Trail,
  requires only the newest selected frame to be open, and binds capture flags to
  that real pool.

`proof_compat_ok` is the only general predicate mentioning `diff_log`; it merely
rules out inert compatibility residue at zero logical depth. It supplies no
capture, extent, reconstruction, or refinement fact.

`hot_defer_wf` no longer requires compatibility ghost contents or coordinate
values to be empty/zero; it remains wholly pool-native. The pointwise accessors
avoid repeatedly exposing nested quantifiers. The bridge
`lemma_wf_implies_hot_defer_wf` requires general `wf`, `TRACK`, unique capture,
and empty Trail/Cold stacks and pools, and establishes `hot_defer_wf` without a
Trail/Cold conversion theorem.

### Exact targeted verification

Every function-scoped query ran from `containers-verus` with `touch src/vec.rs`
immediately before `cargo verus verify -- --triggers-mode silent
--verify-only-module vec --verify-function NAME`. Each listed function reported
`1 verified, 0 errors`:

- H1 accessors/bridge: `lemma_wf_named_parts`, `lemma_hot_repr_at`,
  `lemma_open_ingress_hot_at`, `lemma_wf_implies_hot_defer_wf`, and
  `lemma_index_set_transfer`;
- constructor/dispatch framing: `with_store_mode`, `with_store_policy`,
  `depth_exec`, `frame_saved_len_exec`, `lemma_hot_start_monotone`,
  `lemma_untracked_diff_log_empty`, and the retargeted
  `lemma_phys_cell_eq_overlay`;
- the complete H0 set remained green:
  `lemma_frame_inv_range_capture_append`,
  `lemma_frame_inv_range_set_captured`,
  `lemma_frame_inv_range_set_outside`,
  `lemma_hot_defer_start_monotone`,
  `lemma_hot_defer_cell_eq_overlay`,
  `hot_defer_capture_checked`, `hot_defer_set_checked`,
  `hot_defer_mark_checked`, `hot_defer_restore_zero_checked`, and
  `hot_defer_restore_nonzero_checked`.

The new partition facts make the executable body of `frame_saved_len_exec`
checkable across Cold, Hot, and Trail. Its `external_body` marker was removed.
No marker was added.

### Runtime, formatting, and source checks

- `cargo test -p semi-persistent-containers-verus --test three_tier_runtime`:
  **30 passed**.
- `cargo test -p semi-persistent-containers-verus --test trail_vec`:
  **5 passed**.
- `PROPTEST_CASES=1024 cargo test -p containers-conformance --release --test
  three_tier_policy_matrix`: **4 passed**, including the generated matrix.
- `cargo test -p semi-persistent-containers-verus --features
  "compat-all,literal-types"`: all executed unit/integration/doc tests passed;
  only the maintained stress/measurement/child-scenario tests were ignored.
- `cargo fmt --all -- --check` and `git diff --check`: passed.
- Executable source scan found zero `admit(...)`/`assume(...)` calls.
- Source-derived marker count: **90 default**, plus **5** `literal-types`
  registrations = **95**; delta from H0 is **-6 / -6**. One proved accessor
  marker and five unreachable legacy scaffold markers were removed. Axiom
  counts remain **1 default / 6 literal-types**.
- The separate partial-API checker remains red with the same broad legacy
  allowlist drift (40 reported public partial functions); H1 changed none of
  those APIs and introduced no new public function.

### Full verification resolution

The first full-module runs exposed unreachable legacy proof bodies that encoded
the former two-stack/inert-log model. Those bodies were retired rather than
retargeted because the executable dispatch already returned through its
external runtime path and the old obligations were not conjuncts of the new
`wf`. `lemma_phys_cell_eq_overlay` was retargeted to authoritative
`hot_value_pool` and remains verified.

After that retirement, `maybe_shrink` exposed two genuine H1 framing defects.
First, Cold reconstruction had omitted the per-cell coverage needed for
non-monotone frame lengths. `cold_reconstructs(f)` now states that every
uncovered `c < saved_len(f)` is in bounds of `layer_above_at(f)` and equal to
that layer; a saved cell beyond the layer must therefore be represented by a
Cold run. Second, `open_ingress_ok` constrained capture bits while `TRACK` was
false even though `DiffStore` intentionally leaves untracked bits dead. Those
bit-content clauses are now guarded by `TRACK`.

Named pointwise/transfer lemmas keep both nested invariants solver-controlled.
The following clean queries pass:

```text
lemma_cold_reconstructs_at        1 verified, 0 errors
lemma_cold_reconstructs_transfer  1 verified, 0 errors
lemma_open_ingress_transfer       1 verified, 0 errors
maybe_shrink                      1 verified, 0 errors
full vec module                 117 verified, 0 errors
```

The full gate command was `touch src/vec.rs && cargo verus verify --
--verify-only-module vec`. No `external_body`, `admit`, or `assume` was added to
close H1.

## 2026-09-15 — H2 push/regrowth checked core

**Result: internal Hot-only push/regrowth core verified; runtime/public wiring is
not yet claimed.**

The geometric frame model is now recorded in
`doc/design/17-three-tier-frame-grid.md`. It treats indices as horizontal
columns, frame age as the vertical axis, and each frame's `saved_len` as an
independent boundary. It also records that Hot and Cold payload counts are
bounded by `saved_len`, while a Trail frame may contain arbitrarily many
chronological duplicates until `dedupe_first` establishes the unique Hot bound.
Persistent Hot is unordered; sorting is a transient, local Hot-to-Cold
translation step that preserves uniqueness and the frame abstraction.

`lemma_frame_inv_range_grow_layer` formalizes horizontal extension of the live
row. A captured column is independent of that row; an uncovered column was
already in bounds of the old row and transfers through prefix equality. It
requires no relation between adjacent frame saved lengths.

`hot_defer_push_checked` copies the locked `runtime_push` algorithm: append one
live value and a false capture bit, then restore the bit iff the appended index
is strictly below the active frame's own `saved_len`. Re-entry appends no Hot or
canonical history because the earlier pop already covered that column. The core
preserves `hot_value_pool`, `full_trail`, snapshots, frame coordinates, and
`active_saved_len`, and re-establishes `hot_defer_wf`.

Exact verification from `containers-verus`, touching `src/vec.rs` before each
query:

```text
lemma_frame_inv_range_grow_layer  1 verified, 0 errors
hot_defer_push_checked            1 verified, 0 errors
lemma_captured_in_range_dedupe    1 verified, 0 errors
full vec module                 119 verified, 0 errors
```

`lemma_captured_in_range_dedupe` received only `spinoff_prover` isolation after
the larger module context exhausted its previous shared query; its theorem and
body are unchanged. No `external_body`, `admit`, or `assume` was added.

Scope boundary: `runtime_push` and public `push` remain pre-existing trusted
wrappers, and this checked core currently proves `hot_defer_wf`, not general
`wf`. The next H2 slice must preserve canonical `wf_for_snap`, wire this core
into an in-scope checked dispatcher, and then close pop/set before removing the
public mutator markers.

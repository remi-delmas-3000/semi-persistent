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

## 2026-09-15 — H2 Hot mutators through public wrappers

**Result: unique-capture all-Hot push, pop, and set are checked from general
`wf` through their public wrappers.** Non-Hot Trail/Cold states remain behind
narrow fallbacks whose precondition is the exact negation of the checked
`hot_defer_scope`; those fallbacks belong to later tier milestones.

The proof now maintains two intentionally different histories:

- `hot_value_pool` is authoritative first-capture storage and grows at most once
  per `(frame,index)` column;
- canonical ghost `full_trail` appends one chronological old-value event for
  every in-frame set/pop capture, including duplicates.

`lemma_frame_inv_range_append_duplicate` proves that a later vertical Trail
event preserves the frame's first hitter. `lemma_frame_inv_range_shrink_layer`
and `lemma_frame_inv_range_pop_last` prove horizontal contraction: capture the
departing saved column, while every higher absent saved column was already
forced into the covered arm. `lemma_frame_inv_range_grow_layer` handles push
and re-entry. None assumes adjacent saved lengths are monotone.

`hot_defer_capture_canonical_checked`, `hot_defer_push_checked`,
`hot_defer_pop_checked`, and `hot_defer_set_checked` preserve both
`hot_defer_wf` and general `wf`. `hot_defer_scope_exec` proves the executable
dispatch criterion. Checked `runtime_push`, `runtime_pop`, and `runtime_set`
route the Hot scope to those cores; only `!hot_defer_scope` reaches the trusted
fallbacks. Public `push`, `pop`, and `set_index` now verify without
`external_body`, preserving their prior contracts byte-for-byte.

Exact results:

```text
all new grid/transfer/assembly lemmas       1 verified, 0 errors each
hot_defer_capture_canonical_checked         1 verified, 0 errors
hot_defer_push_checked                      1 verified, 0 errors
hot_defer_pop_checked                       1 verified, 0 errors
hot_defer_set_checked                       1 verified, 0 errors
runtime_push/runtime_pop/runtime_set        1 verified, 0 errors each
public push/public pop/public set_index     1 verified, 0 errors each
full vec module                           134 verified, 0 errors
three_tier_runtime                          30 passed, 0 failed
```

`maybe_shrink` and `lemma_captured_in_range_dedupe` received only
`spinoff_prover` isolation after the larger module context triggered the known
Verus rlimit-statistics panic; their contracts and proof bodies remain checked.
No new trusted body or assumption was added. Removing the three public mutator
markers changes the source-derived count from 90 to **87 default**, plus 5
`literal-types` registrations = **92**.

Next: H3 must connect checked `maybe_shrink` and `hot_defer_mark_checked` through
explicit `RolloverPolicy::Defer` dispatch for both `ShrinkPolicy::Never` and
thresholded shrink, then remove the in-scope mark-wrapper trust.

## 2026-09-15 — H3 explicit Hot Defer marks

**Result: explicit unique-capture all-Hot `RolloverPolicy::Defer` marks verify
through `try_mark_with` for both `ShrinkPolicy::Never` and
`IfOverallocated`.**

`hot_defer_mark_checked` now requires and preserves general `wf` in addition to
the physical Hot projection. A mark seals the prior Hot header, opens an empty
Hot frame, pushes the unchanged live view into `snapshots`, and pushes the
unchanged `full_trail.len()` as the canonical delimiter. The former top's layer
becomes an equal snapshot; the new top range is empty. Equal delimiters preserve
empty-frame token identity, and no adjacent saved-length relation is assumed.

`maybe_shrink` exposes equality of every physical tier sequence.
`hot_defer_post_mark_shrink_checked` checks the post-mark capacity-only calls,
and `hot_defer_mark_with_shrink_checked` composes pre-mark shrink, canonical/
physical mark, and post-mark shrink for both variants. The existing allocator
helpers remain in the documented capacity-only boundary and prove that element
sequences are unchanged.

`runtime_push_frame` is now a checked dispatcher. The explicit Hot+Defer branch
calls the checked composite for either shrink variant. Only the exact complement
`APPLY_CONFIGURED || !hot_defer_scope || !Defer` reaches
`runtime_push_frame_fallback`; shrink is intentionally absent from that
complement. `push_frame_with_options` and `mark_with_options` are checked, so
`try_mark_with` reaches the verified branch without an in-scope trusted wrapper.
Configured and forced rollover remain later milestones.

Exact results:

```text
hot_defer_mark_checked                    1 verified, 0 errors
lemma_wf_for_snap_transfer                1 verified, 0 errors
hot_defer_post_mark_shrink_checked        1 verified, 0 errors
hot_defer_mark_with_shrink_checked        1 verified, 0 errors
runtime_push_frame dispatcher             1 verified, 0 errors
push_frame_with_options                    1 verified, 0 errors
mark_with_options                          1 verified, 0 errors
try_mark_with                              1 verified, 0 errors
full vec module                          140 verified, 0 errors
three_tier_runtime                         30 passed, 0 failed
```

No persistent Hot sortedness is introduced; the mark opens an unordered empty
unique frame. No trust marker or assumption was added. Removing two explicit
mark-wrapper markers changes the source-derived count from 87 to **85 default**,
plus 5 `literal-types` registrations = **90**.

Next: H4 must preserve canonical/general `wf` through zero and nonzero Hot
restore, factor exact-negation restore fallback (including fused Inline replay),
and remove the in-scope `restore_frame` trust.

## 2026-09-15 — H4 canonical history prefix (work in progress)

Fresh checkout baseline at `90f3168`:

```text
cargo verus verify -p semi-persistent-containers-verus
containers package: 2227 verified, 0 errors
vstd dependency:    2044 verified, 0 errors (separate count)

cargo test -p semi-persistent-satcore -p semi-persistent-egraph --locked
exit 0; satcore: 10 passed, 0 failed; egraph suites passed
```

The frame-grid review found missing mandatory coverage in the illustrative
stack and a replay diagram that placed resizing after writes. Chapter 17 now
shows the saved-domain/coverage matrix, resizing before replay over a fixed
target window, and explicit preservation of the surviving canonical prefix.
The sparse-frame equivalence also states its newer-layer input.

The existing nonzero Hot restore helper discarded all `full_trail` entries
while retaining older delimiters and snapshots. This sufficed for its physical
`hot_defer_wf` postcondition, but could not preserve canonical reconstruction.
It now retains `pre.full_trail[..pre.trail_frames[target]]`.
`lemma_restore_canonical_prefix` transfers each surviving canonical frame's
range and newer layer; the new live view equals the former newer snapshot for
the surviving top. Both Hot restore helpers now export general `wf` as well as
the physical projection. Zero restore clears inert compatibility storage to
establish its zero-depth clause; that storage supplies no reconstruction fact.

Targeted checks from `containers-verus`, touching `src/vec.rs` before each:

```text
cargo verus verify -- --verify-only-module vec --verify-function lemma_restore_canonical_prefix
1 verified, 0 errors
cargo verus verify -- --verify-only-module vec --verify-function hot_defer_restore_zero_checked
1 verified, 0 errors
cargo verus verify -- --verify-only-module vec --verify-function hot_defer_restore_nonzero_checked
1 verified, 0 errors
```

This is not an H4 milestone checkpoint. Full Vec re-verification is pending.
Inline fused capture clearing, checked public restore dispatch, full-package
and runtime gates, and trust-marker removal remain. No trust marker or
assumption was added; the public contracts are unchanged.

### H4 follow-up — fused replay and checked public dispatch

The initial canonical-prefix slice passed full Vec verification:

```text
cargo verus verify -- --verify-only-module vec
142 verified, 0 errors
```

`DiffStore` now exposes `restore_entries_clear_capture_spec`, refines the
runtime accessor to it, and preserves the capability across mutations. Its
`restore_overlay` contract additionally states that, for a fused-clear store,
any still-set capture flag names no entry in the replayed range. Inline's
backward replay loop proves this by excluding every already-replayed index;
Parallel and Trail retain their existing non-fused behavior. DynStore delegates
the same capability and postcondition. No store algorithm changed.

Full store-module checks with `cargo verus verify -- --verify-only-module MODULE`:

```text
inline_store:   29 verified, 0 errors
parallel_store: 29 verified, 0 errors
trail_store:    27 verified, 0 errors
dyn_store:      26 verified, 0 errors
```

Both Hot restore helpers now use fused clearing when supported and pre-clearing
otherwise, and establish all-clear before rebuilding survivor capture state.
Each passed a function-scoped check (1 verified, 0 errors). The checked runtime
dispatcher covers all Hot states; only its exact complement reaches the renamed
`runtime_restore_frame_fallback`. The public `restore_frame` contract is
unchanged and its trust marker is removed. Cold allocation reclamation uses the
existing sequence-preserving capacity primitive and the canonical transfer
lemma. The default trust count is now 84 (plus 5 literal-type registrations).

```text
cargo verus verify -- --verify-only-module vec --verify-function '*restore*'
14 verified, 0 errors (includes runtime_restore_frame, restore_frame, restore)
cargo fmt --all -- --check
exit 0
cargo test -p semi-persistent-containers-verus --test three_tier_runtime
30 passed, 0 failed
```

The full-package Verus, feature-test, and 1024-case differential-policy gates
are running. These edits remain uncommitted until those gates pass. This
partial Hot milestone does not discharge mixed-tier fallback trust.

H4 gate update: the feature suite passed (exit 0), and
`PROPTEST_CASES=1024 cargo test -p containers-conformance --release --test three_tier_policy_matrix`
passed all four tests. The generator reads `PROPTEST_CASES`; each generated tape
runs through every profile/backend combination.

The first package-level Verus command reused cached build output and produced
no fresh verification summary. It is NOT counted as a full-package check.
A fresh check was forced with:

```text
touch containers-verus/src/vec.rs
cargo verus verify -p semi-persistent-containers-verus -- --time-expanded
```

That fresh run remains pending; it is the remaining milestone gate before
committing H4.


### H4 checkpoint — all milestone gates passed

The forced full-package invocation above completed with **2232 verified,
0 errors** (4m 52s). This is a fresh package result, not the cached command.
Together with the 30 runtime tests, full `compat-all,literal-types` test suite,
1024-case policy matrix (four tests), formatting, and source-derived 84+5
trust-marker count, it closes H4's gates. No public theorem was weakened.

The checkpoint establishes exact snapshot restoration and surviving-prefix
validity through the real public all-Hot path, including Inline fused capture
clearing and Parallel pre-clearing. The `!hot_defer_scope()` fallback remains
trusted; this is not completion of Trail, Cold, or all-policy proofs.

Next is N2/H5 downstream composition. Inspection has identified missing public
success postconditions in `ListArena::try_restore` and `EClasses::try_restore`,
and missing archive-prefix postconditions in the Map/BPlus public surface.
These should expose already-established internal facts without changing the
runtime algorithms. The full package currently verifies their existing,
weaker contracts against the updated Vec theorem; that alone does not prove
stronger public snapshot-stack guarantees.

## 2026-09-15 — Shared physical frame meaning (in progress)

The user's updated execution plan is preserved in
`all-tier-semi-persistence-goal.md`. It places the shared physical contract and
all-tier Vec closure before the downstream public-contract pass. The H4 local
checkpoint is `b904db2`; no push is authorized.

`range_saved_value` interprets a physical Trail/Hot range as the first
chronological value at an index, or `None` when absent. Its contract is derived
from `frame_cell_inv` and `first_hitter`. `frame_saved_len` reads the appropriate
physical header, and `frame_saved_value` uses Trail/Hot pools or Cold runs.
`lemma_frame_saved_value_contract` derives the same covered/inherited rule for
all three tiers from the existing invariant; it does not add an assumption or
use `diff_log` as storage authority.

`lemma_overlay_saved_value` proves length preservation and the earliest-hit
mapping for backward replay, including duplicate Trail writes. The checked,
inlined `replay_physical_range` exports that meaning alongside the unchanged
DiffStore replay/capture guarantees. The real Trail and Hot replay sites now
call it. `lemma_physical_frame_step` proves the fixed-window telescope step:
within the frame's saved domain the result equals that frame's snapshot, even
when that domain is shorter than the target buffer. The full runtime
composition and Cold replay still need to consume this shared argument.

Targeted Verus evidence (touching `src/vec.rs` before each invocation):

```text
cargo verus verify -- --verify-only-module vec --verify-function '*saved_value*'
2 verified; combined tier bridge exceeded the default resource limit
```

The bridge was then factored to expose only the selected tier, reusing
`lemma_hot_repr_at` for Hot. No resource-limit increase was needed:

```text
cargo verus verify -- --verify-only-module vec --verify-function lemma_frame_saved_value_contract
1 verified, 0 errors
cargo verus verify -- --verify-only-module vec --verify-function replay_physical_range
1 verified, 0 errors
cargo verus verify -- --verify-only-module vec --verify-function lemma_physical_frame_step
1 verified, 0 errors
cargo fmt --all -- --check
exit 0
```

A fresh full-package run (`touch containers-verus/src/vec.rs`, then
`cargo verus verify -p semi-persistent-containers-verus -- --time-expanded`) and
the runtime, feature, and 1024-case policy gates are running. This work is
uncommitted pending those results and is not an all-tier completion claim.

### Shared-frame checkpoint — milestone gates passed

The fresh full-package run completed with **2237 verified, 0 errors** (4m 48s),
five more checked facts than H4. The 30 runtime regressions, full
`compat-all,literal-types` suite, and 1024-case differential matrix (four tests)
all passed. Formatting and `git diff --check` passed. Trust remains 84 default
markers plus five literal-type registrations; no assumptions were added.

This checkpoint establishes the shared interpretation and checked Trail/Hot
range replay. It does not claim the entire mixed-tier orchestrator is checked.
Next: discharge the default Cold `DiffStore::restore_run` path used by Inline
and DynStore, then connect Cold frame replay and the fixed-window telescope.


### Cold run primitive — checked backends

Replaced the trusted default `DiffStore::restore_run` with a required contract
implemented by all four backends. Inline proves a bounded re-encoding loop that
preserves tags even with `TRACK=false`; DynStore delegates to checked Inline,
Parallel, and Trail implementations. Removed the unused trusted usize-write
scaffold. Custom DiffStore implementations must now provide `restore_run`.

A runtime regression first reproduced overflow at `base=u64::MAX` in the old
Inline and dynamic defaults. The fixed loop clamps before addition; all three
regressions now pass, including explicit capture-tag preservation. Targeted
Verus checks report Inline 2 verified and DynStore 1 verified, zero errors.
Trust falls from 84 to 82 default markers (plus five literal-type registrations).
The fresh default full-package run passed: **2240 verified, 0 errors**
(4m 51s). The `compat-all,literal-types` suite passed, including all 30
three-tier runtime tests and the three new regressions. The release differential
policy matrix passed all four tests with `PROPTEST_CASES=1024`. E-graph and
SAT consumer suites passed 1267 tests, with 45 ignored and zero failures.
Formatting, source trust counts, and `git diff --check` passed.

The mixed-tier restore orchestrator is still trusted; checked run copies alone
do not close it.

The fresh `literal-types` Verus run also passed: **2240 verified, 0 errors**
(4m 57s). Both feature configurations were checked from freshly touched source.


### Mixed-tier reconstruction — local pre-state and batched induction

The preceding Cold-run checkpoint is `70cd3ed`. The next reconstruction phase
uses `let ghost pre = *self` and adds no persistent fields or ghost history.
`frame_saved_value` remains a projection of physical pools. Reconstruction is
separate from final well-formedness: intermediate buffers need only agree with
the relevant pre-state layer on their shared index domain.

Cold replay now proves adjacent-run disjointness implies pairwise separation,
composes the checked run copies, bridges the resulting mapping to
`frame_saved_value`, and calls `lemma_physical_frame_step`. A checked reverse
Cold frame traversal preserves the fixed target window even when saved lengths
zigzag. Empty frames need no special logical case.

Trail/Hot replay remains one batched pool overlay per tier. A per-cell induction
uses the captured-or-inherited contract and `lemma_overlay_split` to show that
the batch implements newest-to-oldest frame replay. Narrow layout accessors
supply only required bounds and mapping facts. Profiling identified automatic
unfolding of `wf` as a source of unrelated history instantiations; keeping it
opaque makes the induction verify at the default limit.

`replay_all_tiers_checked` consumes the checked tier results in runtime order.
`reconstruct_target_checked` adds the actual one-time resize and capture
preparation. It returns exactly `pre.snapshots[target]`, preserves every history
field, and preserves store protocols while only decreasing capture flags.
`runtime_begin_restore` is now checked against resized flags and the original
physical ingress pool; its trusted marker is removed. Default trust is 81
markers, plus five literal-type registrations.

The actual mixed-tier fallback calls this reconstruction phase. Its remaining
truncation, canonical-prefix retention, promotion, and capture rebuilding are
still trusted and are not covered by this milestone's completion claim.
Configured/forced/adaptive conversions and mixed-tier mutations also remain.

Targeted checks passed for Cold run composition, the physical/frame bridge,
Cold frame and suffix execution, Trail/Hot layout and cell induction, batched
execution, the mixed-tier replay helper, capture preparation, and the complete
reconstruction wrapper. Fresh default full-package verification passed:
**2259 verified, 0 errors** (3m 24s). Fresh `literal-types` verification also
passed **2259 verified, 0 errors** (3m 26s). The `compat-all,literal-types`
suite passed, including 30 three-tier runtime tests and three Cold regressions.
The release policy matrix passed all four tests with `PROPTEST_CASES=1024`.
The e-graph/SAT consumer suite passed 1267 tests (45 ignored), with zero
failures. Formatting, `git diff --check`, and the 81 + 5 source trust count
passed. All milestone gates are green; the next action is a local signed commit.


Next preservation audit: `cold_repr_ok` currently contains pooled layout,
adjacent-run disjointness, and reconstruction on the saved domain. It does not
explicitly constrain every stored Cold value to that domain or exclude empty
runs. Promotion to a Hot `frame_inv_range` needs the former; the documented
`cold_run_count <= cold_value_count` theorem needs nonempty runs. Establish these
relationships through run formation and preserve them, without adding ghost
history or assuming the relationships. Also export a precise contract for
`cold_value_cut` when verifying physical-prefix truncation.


### Restore prefixes and zero-target closure

The mixed-tier reconstruction checkpoint is `e410180`. Reconstruction now also
ensures every capture flag is clear: pair-tier header monotonicity proves any
replayed ingress suffix contains all originally flagged indices. Fused stores
clear those indices during the existing batch; other stores retain the checked
pre-clear protocol. No extra capture-clearing pass or persistent state is added.

`restored_history_prefix` specifies exact retained Cold, Hot, Trail, snapshot,
canonical-boundary, and canonical-entry prefixes. The checked runtime
`truncate_restored_history_checked` executes the existing tier-specific cuts
and leaves the reconstructed store unchanged. It also establishes
`wf_for_snap`, using the unchanged newer layer of the surviving canonical top.
The Cold value cut now exports its exact physical selector contract.

A regression reproduced a zero-target invariant violation: an allowed nonempty
inert `diff_log` at positive depth survived a Trail zero restore. The restored
value was correct, confirming the shadow was not reconstruction authority.
Zero-target truncation now clears that compatibility vector; nonzero truncation
preserves it. `restore_zero_all_tiers_checked` composes reconstruction, exact
empty-prefix retirement, active-length reset, and existing capacity reclamation
to establish the general invariant for all tier layouts. The dispatcher routes
zero targets through checked paths, and the trusted mixed-tier fallback now
requires a strictly positive target.

Targeted checks passed for capture inclusion/clearing, prefix truncation,
partition and canonical-prefix preservation, zero-target closure, strengthened
reconstruction, and restore dispatch. The fresh default full-package run passed
**2267 verified, 0 errors** (4m 38s). Fresh `literal-types` verification also
passed **2267 verified, 0 errors** (4m 55s). The feature suite passed, including the new zero-depth regression and all
30 three-tier runtime tests. The 1024-case differential matrix passed all four
tests. E-graph/SAT consumers passed 1267 tests (45 ignored), with zero failures.
Formatting, `git diff --check`, and trust-count checks passed. All milestone
gates are green. Trust
remains 81 default markers plus five literal-type registrations: this narrows
the remaining fallback's scope without replacing it with another trusted body.
Nonzero physical-invariant restoration and survivor promotion remain unfinished.


### Retained Trail/Hot representation after truncation

The preceding prefix and zero-target checkpoint is `ee746c2`. The actual
`truncate_restored_history_checked` helper now additionally establishes
`hot_repr_ok` and `trail_repr_ok`. Each retained physical frame keeps its
original range, snapshot, and newer layer. In particular, a newly open top
ends at the same boundary that previously sealed it, and sees the restored
target snapshot as its unchanged newer layer. Unique Hot captures transfer
through equality of the retained pool range.

The proof uses a raw-header-end projection and narrow layout accessors; these
are specifications, not new stored fields. Per-frame transfer and separate
Trail/Hot quantifiers keep unrelated history predicates opaque. The combined
proof passes at the default resource limit. Runtime execution and batching
are unchanged. Cold representation preservation, survivor promotion, and the
remaining nonzero mixed-tier fallback are still unfinished.

Fresh full-package verification passed in both configurations: **2271 verified,
0 errors**, default (4m 52s) and `literal-types` (4m 54s). The
`compat-all,literal-types` suite and all four release differential policy tests
with `PROPTEST_CASES=1024` passed. E-graph/SAT consumers passed 1267 tests
(45 ignored), with zero failures. Formatting and whitespace checks passed.
Trust remains 81 default markers plus five literal-type registrations.


### Retained Cold representation after truncation

The retained pair-tier checkpoint is `6fc2c44`. The checked truncation helper
now also establishes `cold_repr_ok`, so it exports all three physical tier
invariants alongside exact physical/canonical prefixes and `wf_for_snap`.

Frame/run offset monotonicity proves each cut retains complete Cold run slices
and payload ranges. These offset facts do not assume monotone saved lengths.
Explicit covering-run witnesses transfer coverage in both directions; pairwise
run separation makes the selected covering run unique and transfers its value
through the retained payload prefix. The unchanged snapshot/newer-layer lemma
then transfers each retained frame's reconstruction contract, including the
new top and empty frames. No fields, runtime work, or trust markers are added.

Targeted Cold layout, coverage, value, and representation checks pass at the
default resource limit. A full run exposed a resource-limit regression in the
zero-target caller; factoring its final empty-history invariant check into a
small proof resolved the targeted check without increasing limits. Fresh full
verification passed **2278 verified, 0 errors** in both default (4m 54s) and
`literal-types` (4m 53s) configurations. The feature suite passed; the release
differential policy matrix passed all four tests with `PROPTEST_CASES=1024`.
E-graph/SAT consumers passed 1267 tests (45 ignored), with zero failures.
Formatting and whitespace checks passed; trust remains 81 default markers
plus five literal-type registrations.
Survivor promotion/capture rebuilding, conversions, and the remaining public
mixed-tier paths are still unfinished.


### Capture rebuilding and retained-ingress restore

The Cold-prefix checkpoint is `29c2928`. `finish_restore_range_checked` now
proves that flags across the whole live buffer equal membership in the retained
physical frame. It passes the current live length to the store protocol, so
saved lengths may still zigzag or exceed the restored live length.
`finish_survivor_checked` sets the surviving saved length and proves the full
container invariant once the survivor occupies the selected writable tier.
A separate transfer proof preserves all frame contracts through these flag and
cached-length changes. The existing promotion runtime now calls this checked
finalizer; its frame-moving operations remain trusted.

`restore_retained_ingress_checked` composes reconstruction, all-tier truncation,
flag rebuilding, and checked capacity reclamation. Runtime dispatch selects it
when the target leaves a frame in the selected writable tier, including mixed
histories with older immutable Cold/Hot frames. This removes those executions
from the trusted restore fallback. Cases needing Hot-to-Trail or Cold-to-ingress
survivor movement still require promotion proofs. No trust markers or fields
are added, and Trail/Hot replay remains batched.

Targeted range finalization, history transfer, survivor finalization, capacity
reclamation, and retained-ingress composition checks passed. Full default
verification passed **2284 verified, 0 errors** (5m 00s); `literal-types` also
passed **2284 verified, 0 errors** (4m 55s). The feature suite passed, and the
1024-case differential policy matrix passed all four tests. E-graph/SAT consumers
passed 1267 tests (45 ignored), with zero failures. Formatting and whitespace
checks passed. Trust remains 81 default markers plus five literal registrations.
Existing differential tests deliberately
restore through every populated tier for each backend and include shrink/grow
histories; those cover the newly dispatched path and remaining promotion path.


### Checked Hot-to-Trail survivor promotion

The capture-rebuilding checkpoint is `f52541d`. Hot-to-Trail promotion now has
an exact physical postcondition: the Hot prefix is retained, its newest frame's
complete payload moves to a single Trail frame rebased to zero, and all other
fields remain unchanged. The proof preserves the first hitter under rebasing,
the retained Hot frame ranges, the logical frame partition, and all canonical
and Cold contracts. Empty frames retain their header and snapshot identity.
Header-offset ordering supplies bounds without any saved-length ordering.

`promote_hot_survivor_checked` performs the move with one reserve and direct
Copy writes into the retained Trail allocation. This eliminates the temporary
vector and second copy. A regression with a custom Copy value whose Clone
panics exposed a runtime issue with generic cloning: Rust 1.97 specializes slice
extension on TrivialClone, not all Copy types. Direct copies handle both empty
and populated frames without invoking Clone. The regression also writes after
promotion and restores the older token. Batched Trail/Hot replay is unchanged;
no new trusted specification is added.

`restore_hot_promotion_checked` composes reconstruction, exact truncation,
physical promotion, capture rebuilding, and reclamation. Runtime dispatch uses
this path for Trail-discipline restores whose survivor is Hot. The trusted
restore fallback now requires `target <= cold_stack.len()`: its remaining
physical obligation is Cold-to-ingress decoding/promotion. Conversions and
all-tier mutation closure also remain unfinished.

Targeted rebasing, retained Hot range/invariant, complete logical promotion,
executable copying, promotion readiness, and restore composition checks pass.
Final full-package verification passed **2294 verified, 0 errors** in both
default (5m 03s) and `literal-types` (5m 36s) configurations. The feature suite
passed 275 tests (10 ignored), including all 31 three-tier runtime tests and
the new Copy/Clone regression. The 1024-case release differential matrix passed
all four tests. E-graph/SAT consumers passed 1267 tests (45 ignored), with zero
failures. Formatting and whitespace checks passed. Trust remains 81 default
markers plus five literal registrations. Existing runtime tests exercise Hot
promotion, empty frame identity, and write/remigrate after promotion.


### Checked Cold run formation and saved-domain bounds

The Hot-promotion checkpoint is `cc9557e`. Cold promotion requires facts that
were absent from `cold_repr_ok`: emitted runs are nonempty, and every decoded
index lies below that frame's saved length. `cold_payload_ok` now states those
facts without adding stored fields or assuming monotone saved lengths.

The new internal `cold_encode` module checks the actual linear run-formation
loop over sorted unique captures. Its contract preserves both physical pool
prefixes, maps every appended value to its input entry, partitions the input
into maximal consecutive runs, bounds each run by the saved length, and emits
an empty header for an empty frame. The loop groups entries while using index
differences to avoid overflowing a base-plus-length probe. Values use Copy,
never a potentially different user-defined Clone.

`append_cold_sorted_checked` appends the frame header and proves pooled layout,
run disjointness, and saved-domain bounds. Configured and adaptive Hot migration
both call it, replacing their duplicated unchecked run-building loops. Sorting,
complete conversion/refinement, policy orchestration, and Cold promotion remain
unfinished; this checkpoint does not claim those trusted callers are verified.

Pointwise header/run accessors avoid repeated adjacency expansion during frame
assembly. Targeted encoder, frame-layout, payload-bound, disjointness, and
executable append checks pass at the default resource limit. Two runtime tests
pass: prefixed pools with captures near the index limit and an empty frame,
and Copy payloads whose Clone panics. Preservation checks required narrowing
Cold layout/reclamation and capture-finalization proofs: finalization now
requests just the writable top's bounds instead of unfolding every Hot frame.
No resource limits were raised and no trusted markers were added.

Full verification passed **2310 verified, 0 errors** in default (3m 48s) and
`literal-types` (3m 37s) configurations. Feature tests passed 277 tests (10
ignored), including all 31 three-tier runtime tests. The 1024-case release
policy matrix passed all four tests; e-graph/SAT consumers passed 1267 tests
(45 ignored). Formatting and whitespace checks passed. Trust remains 81
default markers plus five literal registrations.

Further leaf work is paused for the top-down conditional composition milestone
in `three-tier-top-down-proof-engineering.md`. Existing proofs will be retained
and classified against the required interfaces only after that composition
works; the top theorem will not be weakened to fit existing helpers.


### Physical storage refines the shared top-down model

The conditional composition and classification checkpoint is `5477152`.
The production crate now imports the same mathematical model used by the
conditional proof. `persistence_frame` derives a finite map from each physical
frame's saved-value lookup; `persistence_model` uses those maps alongside the
existing live view and ghost snapshots. Neither is maintained storage.

The physical-domain theorem proves every Some lookup is below the frame's
saved length, including Cold runs. Thus the bounded finite-map construction
cannot silently drop an out-of-domain payload. The lookup theorem preserves
both membership and value. Existing captured-or-inherited lemmas then establish
`snapshots_ok` for the actual Vec view. The capture and writable lemmas connect
real ingress ownership, active saved length, and live capture flags to the same
map interpretation. Untracked mode has no logical frames.

Pair frame and suffix lemmas prove exact shared-map application for arbitrary
buffers. `replay_persistence_pair_checked` performs the original single pool
batch and exports this effect and the existing capture protocol. The old
snapshot-oriented wrapper calls it and retains its complete contract. Likewise,
`replay_persistence_cold_checked` performs direct run replay and proves the
shared map's exact application; the old Cold frame wrapper retains its snapshot
step contract. No replay loop or batching changes, extra runtime map lookups,
assumptions, or trusted bodies were introduced.

Targeted checks passed for the physical interpretation, capture/writable
bridge, pair composition/execution, and Cold execution. The conditional target
passes 80 obligations with the new finite-map accessor. Full default and
literal-types production verification each passed **2340 verified, 0 errors**.
Feature tests passed 277 tests (10 ignored), the 1024-case differential policy
matrix passed all four tests, and e-graph/SAT consumer tests passed 1267 tests
(45 ignored). Formatting and whitespace checks passed. Trust remains 86 source
markers (81 default plus five literal registrations); the differential oracle
is unchanged. This milestone does not yet instantiate every provisional
interface or complete all-tier public closure. The derived-contract audit
records the initial public wrapper gaps without changing their implementations.

### Exact shared-map retirement and Hot survivor reopening

Physical range equality and subrange rebasing now preserve the complete
earliest-capture lookup, including absence. Retained Cold cells use the existing
coverage/value transfer theorem; retained Trail/Hot cells use the existing exact
range bounds and the new local equality theorem. No intermediate `self.wf()`
premise is needed. The resulting map theorem gives the exact shared frame
sequence prefix and is exported by `truncate_restored_history_checked` alongside
all its previous canonical and physical postconditions.

Hot survivor promotion preserves the whole shared model. The newest frame's
rebased Trail range has the same earliest-capture map as its original Hot range;
older Hot ranges and all Cold storage retain their meanings. The checked
promotion exports this equality. Capture finalization also exports unchanged
shared model via a history framing lemma, while preserving its original full
well-formedness and concrete field-framing contract.

Targeted lookup, rebasing, retained-frame and Hot-promotion lemmas passed. Full
default and literal-types verification each passed **2348 verified, 0 errors**;
the conditional theorem still passes 80 obligations. Feature tests passed 277
(10 ignored), the 1024-case differential policy matrix passed four tests, and
consumer tests passed 1267 (45 ignored). Formatting and whitespace checks passed.
Trust remains 86 source markers; the differential oracle is unchanged. This
milestone adds only erased proofs and contracts, with no executable statement
changes. This remains concrete
interface-discharge work; Cold promotion and the remaining all-tier/public and
derived/parallel obligations are not complete.

### Checked Cold decoder for both writable tiers

`cold_decode::decode_into` now implements the existing nested run/cell traversal
directly into the destination pair pool. Its contract proves exact saved-value
lookup equality with the source runs for every index, strictly increasing
destination indices, saved-domain bounds, and exact output length. A positional
source/destination relation supplies coverage in both directions, including
empty frames and gaps. Index conversion is proved successful; values use Copy.

Both Cold branches in the existing survivor dispatcher call this helper: Hot
for unique-capture stores, Trail for chronological stores. The helper adds no
intermediate pair buffer, runtime map, persistent ghost field, or extra traversal.
Both executable helper boundaries are marked inline(always). Performance has
not been benchmarked; no speedup or slowdown claim is made.

The local decoder's ten obligations and two Vec interpretation/representation
bridge lemmas passed targeted verification. Narrow per-cell lemmas resolved the
initial quantifier/resource failures without raising limits. Full default and
literal-types verification each passed **2360 verified, 0 errors**; the
conditional theorem passed 80 obligations. Feature tests passed 277 (10
ignored), the 1024-case differential policy matrix passed four tests, and
consumer tests passed 1267 (45 ignored). Formatting and whitespace checks passed.
Trust remains 86 source markers and the differential oracle is unchanged.

The surrounding `runtime_promote_survivor` remains trusted. Its Cold source
truncation, destination header publication, older-frame preservation and final
invariant composition still need concrete discharge. Replacing its inner loops
with the checked decoder does not discharge that caller or reduce the trust
count. Existing checked replay, retirement, Hot promotion and capture rebuilding
remain intact.

The promotion caller must establish that the selected destination pool is empty
and that the original survivor header names valid source runs before it is
popped. The retained Cold-prefix proof should use the existing layout accessors
(which require only `repr_ok`) and preserve per-cell coverage/value facts without
assuming an intermediate full `wf`. Header publication must re-establish the
Cold/Hot/Trail frame partition for the store-selected destination before the
existing capture-finalization theorem is applied.

### Checked Cold promotion and complete Cold-survivor restore

The decoder checkpoint is signed local commit `25ecbcf`. The subsequent work
checks the complete promotion assembly for both DiffStore-selected destinations.
`promote_cold_storage_checked` proves the exact Cold prefixes, unchanged store
and canonical fields, decoded destination contents, and the new survivor header.
`cold_survivor_promoted` records that intermediate effect without assuming full
well-formedness. Partition, older Cold representation, destination representation
and shared-map equality are then proved separately.

The Cold prefix proofs were adapted to require physical representation rather
than full `wf`. Their original restore contracts remain as checked wrappers.
Saved-value transfer uses explicit header/run accessors to stay within existing
resource limits. The decoded destination satisfies the original pair-frame
invariant and uniqueness; no snapshot or map contract was weakened.

`restore_cold_survivor_checked` now composes reconstruction, exact retirement,
checked Cold promotion, capture finalization and reclamation. It retains the old
public-facing contents/depth/snapshot-prefix effects and additionally exports
the exact retained shared-frame prefix. Capacity reclamation now exports shared
model and canonical-history preservation. The original specialized Hot proofs
remain checked.

All 45 selected Cold obligations and the shared-view framing lemma passed. Only
then was the obsolete trusted `runtime_promote_survivor` removed. The former
`runtime_restore_frame_fallback` is now the checked Cold restore function.
This removes two markers: **79 default + 5 literal registrations**, with no new
trusted body or axiom. CI and the trust ledger are updated together. Full default
and literal-types verification each passed **2373 verified, 0 errors**; the
conditional target passed 80 obligations. Feature tests passed 277 (10 ignored),
the 1024-case differential matrix passed four tests, and consumer tests passed
1267 (45 ignored). Formatting and whitespace checks passed. The differential
oracle is unchanged.

An additional CI partial-API audit fails with 73 public partial functions,
33 allowlisted and 40 unlisted (zero unsafe-public functions). Running the
same scanner against the committed `25ecbcf` source produced exactly the same
output and exit status. This change adds no public partial API; the pre-existing
allowlist discrepancy remains recorded rather than being hidden by expanding
the allowlist. The trust-count CI check passes at 79 + 5.

This closes the remaining trusted Cold restore implementation boundary. It does
not discharge all-tier mutation/mark/rollover fallbacks, the complete production
interface instantiation, or derived and parallel container closure. Those remain
part of the active objective.

### General canonical capture and checked mark wrapper

The nightshift resumes from `d191c4a` under the detailed acceptance checklist in
`semi-persistence-completion-goal.md` and the execution instructions in
`nightshift-completion-goal.md`. All four completion milestones remain open.

`lemma_canonical_capture_append` separates canonical-history preservation from
Hot-only physical assumptions. It proves chronological append preservation,
including duplicate captures and all older strata, from `wf_for_snap`, unchanged
live/snapshot/boundary views and the physical caller's partition. Existing
first-capture, duplicate and unchanged-range lemmas are reused. The original
Hot canonical capture helper now calls this general lemma with its unchanged
contract; its no-append branch reuses canonical repartition framing.

The legacy `push_frame` wrapper verifies against the existing dispatcher
contract, removing one redundant `external_body`. The dispatcher still depends
on the trusted all-tier mark fallback. Trust is **78 default + 5 literal
registrations**; CI and the trust ledger agree, and axioms are unchanged.
These edits change only proof code and verification annotations, with no
executable statement changes or new resource limits.

Evidence:

- Selected capture proofs: 16 verified, zero errors
  (`/tmp/sp-d21-canonical-capture-reuse.log`). The new general lemma verified
  independently before its use replaced the specialized proof block.
- Selected mark wrapper/dispatcher proofs: 3 verified, zero errors
  (`/tmp/sp-d21-mark-wrapper.log`).
- Full default and literal-types: **2375 verified, zero errors** each
  (`/tmp/sp-d21-capture-general-default.log`,
  `/tmp/sp-d21-capture-general-literal.log`).
- Conditional composition: 80 verified, zero errors
  (`/tmp/sp-d21-capture-general-conditional.log`).
- Feature tests: 277 passed, 10 ignored
  (`/tmp/sp-d21-capture-general-features.log`). Formatting and whitespace checks
  passed; the source trust count matches 78 + 5.

Commands retain the previous milestone's form: `cargo verus verify -p
semi-persistent-containers-verus -- --time-expanded`, the same command with
`--features literal-types`, direct `verus --crate-type lib
containers-verus/proofs/top_down/composition.rs`, and `cargo test -p
semi-persistent-containers-verus --features 'compat-all,literal-types'`.
The differential oracle is unchanged. Consumer/differential suites and performance
benchmarks were not rerun for this proof-only checkpoint; final revision gates
and benchmark parity remain required, as does the recorded partial-API audit.

Next: prove the physical capture effect and membership preservation for both
ingress disciplines, then compose with the general canonical lemma. The regrowth
audit found that Trail's ghost flag is cleared by `TrailStore::push` but the
trusted Vec fallback only calls `mark_captured` for unique stores. The general
push proof must restore Trail's ghost membership when reentering a saved domain,
without weakening the invariant or adding runtime flag overhead. This obligation
is recorded in the proof classification alongside the existing capture gaps.

### Checked all-tier physical capture through DiffStore

Starting from signed checkpoint `96c90f9`, `runtime_capture` now verifies for
both store-selected ingress disciplines under the general Vec invariant. The
old trusted capture boundary is removed. Its contract exports exact physical
append/no-op behavior, unchanged nonselected pool, capture-flag update, unchanged
live contents, canonical event append and all three immutable store protocol
predicates. Outside the active saved domain, the whole state is unchanged.

`ingress_capture_effect` describes only the intermediate physical mutation.
`lemma_ingress_capture_frame` handles a single Hot or Trail frame using the
existing first-capture, duplicate and unchanged-range proofs. Separate Hot and
Trail representation lemmas expose header triggers narrowly. Capture flags,
Cold framing and canonical preservation compose to recover `wf`. The previous
checkpoint's general canonical-append lemma then supplies the chronological
event proof. A separate full-trail framing lemma proves that this ghost-only
event leaves physical predicates unchanged.

The physical frame and final flag arguments verified before integration.
Resource failures were resolved by splitting tier/header obligations, hiding
irrelevant reconstruction definitions and explicitly supplying store
well-formedness where `wf_for_snap` was hidden. No solver limits were raised.
The original specialized Hot capture proofs remain checked and intact.

Both runtime branches now call `DiffStore::capture`. The Trail implementation
continues to append duplicates unconditionally and maintains capture flags only
in ghost code. Unique capture uses the same store primitive without invoking a
Hot-only helper under a weaker premise. No persistent fields, maps, buffers or
traversals were added. The call-path change has not been benchmarked; performance
parity remains a required final gate.

Evidence on this source revision:

- Selected capture family: **23 verified, zero errors**
  (`/tmp/sp-d21-ingress-runtime-final.log`); separate full-trail physical framing:
  one verified, zero errors (`/tmp/sp-d21-ingress-framing2.log`).
- Full default and literal-types verification: **2383 verified, zero errors**
  each (`/tmp/sp-d21-ingress-default.log`, `/tmp/sp-d21-ingress-literal.log`).
- Conditional composition: **80 verified, zero errors**
  (`/tmp/sp-d21-ingress-conditional.log`).
- Feature tests: **277 passed, 10 ignored**
  (`/tmp/sp-d21-ingress-features.log`).
- Release differential policy matrix with `PROPTEST_CASES=1024`: **4 passed**
  (`/tmp/sp-d21-ingress-policy.log`).
- E-graph/SAT-core consumers: **1267 passed, 45 ignored**
  (`/tmp/sp-d21-ingress-consumers.log`).
- Formatting, whitespace and trust-count checks passed. Trust is now
  **77 default + 5 literal registrations**, with unchanged axiom counts and
  synchronized CI/trust documentation. The legacy `containers/` tree is unchanged.

Commands use the previous full-gate sequence: default and literal-types
`cargo verus verify -p semi-persistent-containers-verus -- --time-expanded`,
direct `verus --crate-type lib containers-verus/proofs/top_down/composition.rs`,
`cargo test -p semi-persistent-containers-verus --features 'compat-all,literal-types'`,
`PROPTEST_CASES=1024 cargo test -p containers-conformance --release --test three_tier_policy_matrix`,
and `cargo test -p semi-persistent-egraph -p semi-persistent-satcore`.

The additional partial-API audit still fails with 73 public partial functions,
33 allowlisted and 40 unlisted, zero unsafe-public. Its output in
`/tmp/sp-d21-ingress-partial-api.log` is byte-for-byte identical to the recorded
baseline audit; no allowlist entries were added. This remains an open final-audit
item, not a claim that all CI gates pass.

Next: compose this checked capture with `set_raw` and the existing captured-cell
and outside-saved-domain write lemmas for general mixed-tier set. Pop and
regrowth still need their general preservation proofs, including Trail's ghost
flag restoration on regrowth. Explicit shared-map `capture_first` equality is
still required for the production interface. Mutation/mark, migration/policy,
complete interface instantiation, derived/parallel closure and benchmark parity
remain open; this checkpoint does not complete any of the four overall steps.

### Checked mixed-tier set through capture and raw write

Starting from signed checkpoint `122a5b7`, `runtime_set_fallback` now verifies
against its original contract. Both ingress disciplines compose the checked
general capture path with `DiffStore::set_raw`. The former unique-store branch
no longer calls a Hot-only helper under a weaker mixed-history premise. The
specialized Hot set proof and its existing fast-path dispatch remain checked.

`raw_set_effect` specifies the exact live update, field framing and immutable
store protocols. Capture-flag equality is TRACK-conditional, matching the
existing DiffStore contract: untracked inline writes are not required to retain
irrelevant tag bits. This preserves supported untracked behavior without adding
flag preservation overhead or weakening any public persistence contract.

The frame proof reuses existing captured-cell and outside-saved-domain write
lemmas. Separate Hot/Trail representation proofs retain all headers, pools and
uniqueness. Pointwise canonical access supplies the newest saved length and
frame contract; older canonical layers are unchanged. A narrow capture-domain
accessor supplies the appended canonical event's range bounds to the executable
wrapper. The final composition recovers all of `wf`, including ingress and Cold
reconstruction. Resource failures were resolved by narrow accessors, explicit
coordinate equalities and local invariant exposure, without increased limits.

`lemma_cold_reconstructs_layer_transfer` adapts the existing Cold framing proof
to require equality of the immediate newer layer rather than the whole live
vector. Older Cold frames therefore survive writes above them. The original
whole-live-equality contract is retained as a checked wrapper; no verified caller
loses its old guarantees.

Evidence on the final source for this checkpoint:

- Selected set family: **18 verified, zero errors**
  (`/tmp/sp-d21-set-runtime5.log`). Cold layer transfer and its existing wrappers
  passed three selected obligations (`/tmp/sp-d21-set-cold-layer.log`).
- Full default and literal-types: **2393 verified, zero errors** each
  (`/tmp/sp-d21-set-default.log`, `/tmp/sp-d21-set-literal.log`).
- Conditional composition: **80 verified, zero errors**
  (`/tmp/sp-d21-set-conditional.log`).
- Feature tests: **277 passed, 10 ignored** (`/tmp/sp-d21-set-features.log`).
- Release differential policy matrix with `PROPTEST_CASES=1024`: **4 passed**
  (`/tmp/sp-d21-set-policy.log`).
- E-graph/SAT-core consumers: **1267 passed, 45 ignored**
  (`/tmp/sp-d21-set-consumers.log`).
- Formatting, whitespace and source trust-count checks passed. The legacy
  `containers/` tree is unchanged. The gate commands are the same full sequence
  recorded for the preceding capture checkpoint.

The set fallback's trust marker is removed. Counts are **76 default + 5 literal
registrations**, with unchanged axioms and synchronized CI/trust documentation.
The partial-API audit remains at 73 public partial functions, 33 allowlisted,
40 unlisted and zero unsafe-public; its output is identical to the preceding
checkpoint (`/tmp/sp-d21-set-partial-api.log`). That final-audit issue remains open.

The new [performance inventory](conformance-performance-inventory.md) reviews all
13 registered Criterion targets. It distinguishes matched legacy comparisons
from tier-specific controls and local algorithm experiments, and records the
parallel-group coverage gap. No timing measurements or parity claim accompany
the inventory; the final benchmark gate remains required.

Next: general push/regrowth and pop preservation. Reuse grow/shrink frame lemmas
and the new Cold-layer transfer; preserve capture membership on saved-domain
regrowth for Trail as well as Hot. Mark, migration/policy, full shared-map
interface instantiation and derived/parallel closure remain open. None of the
four overall completion steps is declared complete by this checkpoint.

### Checked all-tier push/regrowth and pop

Starting from signed checkpoint `f994e18`, both remaining mutation fallback
bodies now verify: `runtime_push_fallback` and `runtime_pop_fallback`. Capture,
set, push/regrowth and pop therefore have checked general implementations in
addition to the retained Hot specializations. Mark/open-frame and policy
execution still require discharge, and the shared-model adapter remains incomplete.

Push preserves every history field, appends exactly one live value and preserves
all three store protocol predicates. Existing grow-layer lemmas preserve pair
and canonical reconstruction. `lemma_push_reentered_capture` proves that a
saved-domain column absent from the old live layer must already be captured.
Regrowth restores capture membership through `mark_captured` for both Hot and
Trail disciplines. This discharges the previously recorded Trail ghost-flag gap.
The Trail hook changes only ghost state; no runtime tag or persistent history
is added. The generic execution guard no longer tests unique capture before
calling that existing hook. Its performance remains subject to the final gate.

Pop captures a disappearing saved-domain value through checked `runtime_capture`
before calling the actual store pop method. The existing last-cell contraction
lemma preserves pair and canonical reconstruction. Older Cold layers are framed
through the newer-layer transfer lemma. Empty pop returns without mutation;
saved-domain index conversion is proved successful from the active-length bound.
Untracked flag behavior retains the original store contract. Neither operation
adds a buffer, map or traversal, and no public contract is weakened.

The first full verifier attempt exposed a resource failure in the existing
canonical-frame accessor (2408 verified, one error). The accessor was decomposed
into frame-contract and saved-length accessors; its original contract remains
unchanged. All three then verified independently. The final full runs below
passed with no increased resource limits, new trust or new axioms.

Final evidence:

- Selected push family: **18 verified, zero errors**
  (`/tmp/sp-d21-push-runtime.log`).
- Selected pop family: **12 verified, zero errors**
  (`/tmp/sp-d21-pop-runtime.log`).
- Decomposed canonical accessors: **3 verified, zero errors**
  (`/tmp/sp-d21-push-pop-accessor2.log`).
- Full default and literal-types verification: **2411 verified, zero errors**
  each (`/tmp/sp-d21-push-pop-final-default.log`,
  `/tmp/sp-d21-push-pop-final-literal.log`).
- Conditional composition: **80 verified, zero errors**
  (`/tmp/sp-d21-push-pop-final-conditional.log`).
- Feature tests: **277 passed, 10 ignored**
  (`/tmp/sp-d21-push-pop-final-features.log`).
- Release differential policy matrix, `PROPTEST_CASES=1024`: **4 passed**
  (`/tmp/sp-d21-push-pop-final-policy.log`).
- E-graph/SAT-core consumers: **1267 passed, 45 ignored**
  (`/tmp/sp-d21-push-pop-final-consumers.log`).
- Formatting, whitespace and trust-count checks passed. The commands are the
  same full gate sequence recorded for the capture checkpoint. `containers/`
  is unchanged both in the worktree and relative to baseline `d191c4a`.

Two trust markers are removed: **74 default + 5 literal registrations**, with
unchanged axioms and synchronized CI/trust documentation. The additional
partial-API audit still reports the same 73 public partial functions, 33 allowed,
40 unlisted and zero unsafe-public; its output is identical to the set checkpoint
(`/tmp/sp-d21-push-pop-partial-api.log`). That audit and benchmark parity remain open.

Next is general mark opening. The caller audit found an omitted TRACK premise
in the internal mark dispatcher/fallback; both actual callers already require
TRACK. Propagate that premise internally, preserve public guards, and prove
prepare/seal/open using the borrowed active range and the transfer of the old
live layer to the equal new snapshot. Replace the invalid Hot-only shortcut for
unique stores with older Cold history. Policy and reclamation calls must compose
after opening, and mark is not complete until those dependencies verify.

## General mark preparation through DiffStore

The internal `runtime_push_frame` and fallback now require TRACK, matching both
existing public-facing callers. This corrects an omitted internal premise without
changing public guards or runtime behavior.

`prepare_mark_range_checked` translates active physical-range coverage into the
borrowed-slice witness required by `DiffStore::prepare_mark`.
`prepare_mark_checked` selects Hot or Trail from the store discipline, handles
zero depth with clear flags, and proves exact framing of every field except the
store. Store data and all three protocol predicates are preserved; all live
capture flags are cleared. The fallback now calls this checked preparation
instead of constructing an unchecked slice inline. No allocation or traversal is
added. The intermediate contract intentionally does not claim container wf:
opening the new empty frame must restore capture-map agreement.

Selected verification: **2 verified, zero errors**
(`/tmp/sp-d21-mark-prepare.log`). Full gate results are recorded below when
available. This does not remove the fallback's trust marker: sealing, empty-frame
opening, the invalid mixed-history Hot shortcut, and actual policy dependencies
remain to be discharged. Existing specialized Hot proofs remain intact.

Checkpoint validation: full default **2413 verified, zero errors**
(`/tmp/sp-d21-mark-prepare-default.log`); feature regression tests completed
successfully (`/tmp/sp-d21-mark-prepare-features.log`). Formatting and whitespace
checks pass, and `containers/` remains unchanged from `d191c4a`. Trust markers
are unchanged. Literal-types verification, differential policy tests and consumer
checks will be rerun with the completed frame-opening milestone; their previous
checkpoint results are not claimed as verification of this revision. Final
benchmark parity remains open.

## Mark structural transition and canonical reconstruction

The actual fallback now uses checked `open_mark_headers_checked` after checked
preparation. The helper seals only the selected newest pair header, appends an
empty header to the DiffStore-selected tier, appends the snapshot and canonical
boundary, and updates the active saved length. Its contract states the exact
header sequences (old last header updated, then one header pushed), exact
snapshot/boundary appends, unchanged unrelated fields, and the final frame
partition. Indexed header updates replace equivalent `last_mut` sugar; no new
traversal, buffer, or runtime history is introduced.

`lemma_canonical_mark_frame` and `lemma_canonical_mark` prove reconstruction
across snapshot/boundary append independently of physical tier placement. They
require the canonical pre-invariant and the post-partition, not an all-Hot model.
After these replacements verified, the existing `hot_defer_mark_checked` was
changed to call the shared canonical theorem instead of duplicating the proof.
The specialized function retains its full contract and verifies with the reuse.

Targeted evidence:

- Canonical helpers: **2 verified, zero errors**
  (`/tmp/sp-d21-mark-canonical2.log`). The initial attempt exposed a missing
  snapshot-count/boundary-count equality; explicitly accessing that existing
  canonical fact resolved the failure without increasing solver limits.
- Existing Hot mark with shared proof: **1 verified, zero errors**
  (`/tmp/sp-d21-mark-canonical-reuse.log`).
- Actual header-opening helper: **1 verified, zero errors**
  (`/tmp/sp-d21-mark-headers.log`).

Still required: use the exact header transition to preserve physical Hot/Trail
ranges, uniqueness, Cold reconstruction, and empty active capture membership;
compose with canonical preservation to obtain general wf. Then replace the
invalid mixed-history Hot shortcut and discharge rollover/reclamation calls.
The fallback remains trusted, and this checkpoint does not close Step 1 or 2.

Structural checkpoint full evidence: default **2416 verified, zero errors**
(`/tmp/sp-d21-mark-structure-default.log`); feature regression suite **277 passed,
10 ignored** (`/tmp/sp-d21-mark-structure-features.log`). Formatting and whitespace
checks pass; the legacy `containers/` tree is unchanged from `d191c4a`. No trust
marker or solver limit changed. Literal-types verification and broader policy/
consumer gates remain due for the completed general opening milestone; final
performance acceptance is still open.

## Physical frame meaning across mark opening

`open_mark_headers_checked` now additionally exports unchanged logical offsets,
starts and effective ends for every old pair frame, plus the selected new frame's
empty range and incremented tier count. These facts are checked against the
actual indexed header updates, rather than assumed by a separate model.

`lemma_mark_pair_frame` uses those coordinate facts to preserve an older Trail
or Hot frame's reconstruction contract after snapshot append; Hot uniqueness is
preserved as well. The prior top's layer changes from live contents to an equal
snapshot, so the same proof handles both the top and older frames.

`lemma_mark_cold_repr` preserves the entire Cold representation across mark.
It uses the new `lemma_cold_reconstructs_frame_transfer`, which needs equality of
only the relevant snapshot and immediately newer layer, plus unchanged physical
Cold storage. The existing layer-transfer contract remains intact as a checked
wrapper. No existing caller loses a guarantee and no runtime body changes in
this checkpoint.

Targeted validation: mark selection **17 verified, zero errors**
(`/tmp/sp-d21-mark-ranges.log`); Cold selection **48 verified, zero errors**
(`/tmp/sp-d21-mark-cold.log`). No trust or solver limit changes.

Next: aggregate the old-frame lemmas and new empty-frame facts into Hot/Trail
representation preservation, establish cleared-flag ingress and compatibility,
and combine with canonical preservation into general wf. The trusted mark
fallback and policy dependencies remain open; these lemmas alone do not complete
mark or the production end-to-end theorem.

Full checkpoint results: default and literal-types each **2419 verified, zero
errors** (`/tmp/sp-d21-mark-physical-default.log`,
`/tmp/sp-d21-mark-physical-literal.log`); conditional composition **80 verified,
zero errors** (`/tmp/sp-d21-mark-physical-composition.log`). Formatting and
whitespace checks pass, and `containers/` is unchanged from `d191c4a`. This
checkpoint contains only proof/specification changes, so runtime regression tests
were not repeated; the preceding structural checkpoint recorded 277 passing
feature tests. Benchmark parity remains unmeasured and required.

## General mark opening and explicit Defer dispatch

`mark_open_effect` is a local specification of the exact existing header/store
transition, not stored ghost history. `lemma_mark_hot_repr` and
`lemma_mark_trail_repr` aggregate old-frame preservation and new empty-frame
reconstruction; `lemma_mark_ingress` establishes cleared-flag agreement and proof
compatibility. `lemma_mark_preserves` combines these with the existing canonical
and Cold preservation lemmas to establish full general wf.

`open_mark_checked` executes actual DiffStore preparation and header opening and
proves this effect plus the public snapshot/depth result. `mark_defer_checked`
composes pre-mark shrinking, opening and checked post-mark reclamation. The actual
dispatch now uses this path for every explicit Defer mark outside the retained
Hot specialization, including older Cold history and chronological stores.

The fallback uses the same checked opening/reclamation. Its invalid Hot-only
shortcut has been removed. A first attempt to check the entire fallback exposed
unsupported direct `shrink_to_fit` calls; these now use the existing
`shrink_vec_capacity(..., 0, 1)` capacity primitive, as restore already does.
Reclamation was separated to avoid broad invariant expansion after a resource
failure, without raising limits. The resulting dispatch attempt identified the
remaining semantic gap: `runtime_apply_configured_rollover` and
`runtime_rollover_on_mark` have no preservation contracts. No assumed contracts
were added to them. The configured/forced fallback retains its existing trust
marker until concrete policy preservation is proved.

Targeted mark checks: **25 verified, zero errors**
(`/tmp/sp-d21-mark-defer.log`). Trust counts and axioms are unchanged. Full gate
results follow below. Runtime changes preserve the pre-shrink/open/rollover/
post-shrink order and add no traversal or allocation. Final benchmark parity
remains required, including any effect from the dispatch/helper refactoring.

General opening checkpoint evidence:

- Full default and literal-types: **2426 verified, zero errors** each
  (`/tmp/sp-d21-mark-general-default.log`, `/tmp/sp-d21-mark-general-literal.log`).
- Feature regression suite: **277 passed, 10 ignored**
  (`/tmp/sp-d21-mark-general-features.log`).
- Release differential policy matrix with `PROPTEST_CASES=1024`: **4 passed**
  (`/tmp/sp-d21-mark-general-policy.log`).
- Conditional composition: **80 verified, zero errors**
  (`/tmp/sp-d21-mark-general-composition.log`).
- Formatting/whitespace pass; trust remains **74 default + 5 literal**;
  `containers/` is unchanged from `d191c4a`.

Step 1 remains open for configured/forced mark's actual policy dependencies and
shared-model interface closure. Next discharge closed-prefix Trail-to-Hot and
Hot-to-Cold migration and assembly, then their policy selectors/execution. Derived
and parallel closure, final consumer/CI audits and benchmark parity remain due.

## Trail migration: exact selected-position publication

`append_selected_hot_frame_checked` now implements the ordinary Trail migration's
existing per-position payload copy and header append. The checked contract gives
exact destination concatenation, exact header append (saved length and bounds),
and full optional saved-value equality between the appended physical range and
the selected payload for every index. Empty selections and nonempty destination
prefixes are covered. Source pools, sorting and selected-position computation
remain in the existing caller; this helper introduces no intermediate payload or
new traversal. Indexed iteration replaces the original iterator loop over the
same selected positions.

Targeted result: **2 verified, zero errors**
(`/tmp/sp-d21-migrate-selected-map.log`). The caller's selection-bounds premise
still needs discharge together with earliest-capture selection, uniqueness,
source retirement/rebasing, and the final global invariant. No migration or policy
trust marker has been removed by this partial assembly proof.

The adaptive bulk-copy path was inspected but remains unchanged. In the pinned
vstd `std_specs/vec.rs`, `Vec::extend_from_slice` guarantees exact length/prefix
but only `cloned(source, destination)` for appended cells. An attempted exact
payload equality proof failed (`/tmp/sp-d21-migrate-hot-append.log`). Generic
`T: Copy` alone does not expose the needed equality through that specification.
No stronger payload bound, assumed clone identity, trusted wrapper, or slower
replacement copy loop was introduced to conceal this gap. Resolve that library
contract/implementation connection before claiming adaptive payload assembly.

Follow-up ownership audit: `runtime_execute_trail_plan` has one caller in
`runtime_apply_adaptive`; it records the frame count before execution and drops
`trail_plan` immediately afterward. No payload is read after execution. This
supports a concrete next step: consume each owned temporary frame through the
already specified `Vec::append`, preserving bulk transfer and avoiding the weak
clone contract. Validate that change and its performance before treating adaptive
assembly as closed. This is an implementation option, not a proved result yet.

Selected publication checkpoint validation: full default **2428 verified, zero
errors** (`/tmp/sp-d21-migrate-append-default.log`); feature tests **277 passed,
10 ignored** (`/tmp/sp-d21-migrate-append-features.log`); release differential
policy matrix with `PROPTEST_CASES=1024` **4 passed**
(`/tmp/sp-d21-migrate-append-policy.log`). Formatting/whitespace pass and the legacy
reference is unchanged. Trust counts are unchanged. Literal-types verification,
consumer tests and final audits remain due with completed migration; benchmark
parity remains an open acceptance criterion.

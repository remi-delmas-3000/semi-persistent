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

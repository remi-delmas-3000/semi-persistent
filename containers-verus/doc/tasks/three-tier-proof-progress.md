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

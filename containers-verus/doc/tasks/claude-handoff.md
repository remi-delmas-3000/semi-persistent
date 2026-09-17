# Handoff to Claude — verified semi-persistence

Updated 2026-09-16. This is a continuation handoff, **not a completion report**.
Inspect the current worktree and logs before relying on the snapshot below.

## Objective and non-negotiable constraints

Finish all four milestones in `containers-verus/doc/tasks/nightshift-completion-goal.md`
and every acceptance criterion in `semi-persistence-completion-goal.md`:

1. Actual mixed-tier mutation and mark for every supported DiffStore.
2. Actual conversions and arbitrary legal rollover-policy sequences.
3. Production instantiation of the complete public-operation sequence theorem.
4. Derived containers and sequential/parallel groups, final verification/tests/CI/trust
   audits, and measured benchmark parity against the unchanged legacy code.

The user expressly requires preserving existing code and verified proofs: establish
strong top-down contracts, reuse matching proofs, adapt insufficient contracts, and
replace incompatible proofs only after replacements verify. Do not weaken the
public theorem to make leaves easier. Do not restart from scratch.

- **DO NOT PUSH TO ORIGIN.** Local signed commits and access to the user's GPG key
  are authorized. Nothing was pushed during this work.
- Keep `containers/` unchanged as the correctness/performance oracle.
- Add no proof holes, assumptions, axioms, trusted semantic wrappers, persistent
  ghost history, or increased solver limits.
- Preserve batching, direct Cold replay, duplicate Trail appends, payload bounds,
  public token/error semantics, and runtime complexity/performance.
- Writable tier is selected by the actual DiffStore discipline. Cold may reopen
  into Hot or Trail. Keep rollover selection distinct from writable-tier selection.
- No subagents unless the user explicitly authorizes delegation.
- Do not declare completion from conditional proofs or passing tests alone.

The original active-goal attachment is:
`/Users/remidelmas/.codex/attachments/98b33d09-4a01-456d-83d4-035af777bdaa/pasted-text-1.txt`.
Read it and the linked acceptance checklist before continuing.

## Repository and current checkpoint

- Working directory: `/Users/remidelmas/projects/sp-d21-exec`
- Branch: `d21-exec`; commits are local and signed; **nothing is pushed**.
- `e28ac37` committed the (since superseded) sort-based Trail selection
  helpers; the Trail-dedupe checkpoint that follows it replaces that algorithm.

## Trail-dedupe checkpoint (2026-09-16)

User direction: the Trail-to-Hot dedupe must be the smallest algorithm — a
left-to-right fold through a hash set keyed by the generic index type `I`
(first capture wins), writing straight into the Hot pool; no `usize`-widened
key buffers, no positions buffer, no plan vectors, no sorting. Hot-to-Cold is
where a slice sort belongs, and it must be std's in-place sort under a trusted
std contract, not a verified insertion sort.

Implemented and verified (see `three-tier-proof-progress.md`, last section):
`trail_select::dedupe_trail_range`; `IndexLike::lemma_obeys_key_model`;
`trail_migrating`/`trail_tentative` with the per-frame primitives
`trail_frame_tentative/commit/discard_checked` and
`trail_migration_finish_checked`; checked `runtime_migrate_trail_count`,
`runtime_migrate_trail`, `retained_closed_prefix`, `adaptive_trail_stage_checked`
(called from the still-external `runtime_apply_adaptive`); Verus-native `Ratio`
with a proved `accepts`. Trust: 68 default + 5 literal `external_body` markers
(CI `EXPECTED_DEFAULT=68`); default axioms 1 -> 4 (`DenseId31`, `DenseId63`,
`DenseUsize` key model) plus one generated per `define_id*!` id type.

## Hot-to-Cold checkpoint (2026-09-16)

Closed Hot frames are sorted in place in the Hot pool (std unstable sort under
the trusted `std_sort::sort_pairs_by_index` contract, the one new trusted item)
and encoded into Cold straight from the slice; the copies, plan vectors and the
run-count scratch are gone. Checked: `hot_frame_sort/encode_checked`,
`hot_migration_finish_checked` (+ `lemma_hot_migration_wf`),
`reclaim_after_hot_migration_checked`, `runtime_migrate_hot_count`,
`runtime_migrate_hot`, `adaptive_hot_stage_checked`; `sort_frame_by_index` now
uses the std contract too. Trust: 64 default + 5 literal (CI
`EXPECTED_DEFAULT=64`).

## Remaining runtime waste from the audit

- `runtime_closed_history_bytes` is recomputed three times per adaptive pass.
- `diff_compress::dedupe_first` is quadratic but has no runtime callers.
- `sort_frame_by_index` still returns a sorted copy (its `(&Vec) -> Vec` API);
  `ColdStack::seal_runs` callers could sort their own buffer in place.

## Policy-dispatch checkpoint (2026-09-16)

All rollover dispatch is checked: `runtime_closed_history_bytes`,
`runtime_reclaim_adaptive_tier_capacities`, `runtime_apply_adaptive` /
`apply_adaptive`, `runtime_apply_tier_policy` / `apply_tier_policy`,
`flush_trail`, `compress_hot`, `runtime_apply_configured_rollover`,
`runtime_rollover_on_mark`, `runtime_push_frame_fallback`. Trust: 53 default +
5 literal (CI `EXPECTED_DEFAULT=53`); the four public wrappers are listed in
`partial-api-allowlist.txt`. The remaining `vec.rs` markers are byte
reporters/diagnostics and transparent type registrations.

## Derived and Step 3 checkpoints (2026-09-16)

`328c512` exports derived restore effects (ListArena, EClasses, SpMap,
CircularList, UnionFind, BPlusTreeSet) and group member models/archives
(`SyncMember::model`/`archive`, `ForkHistory::mark`/`restore`, parallel
variants over the documented rayon boundary). `9df28cb` checks
`pending_restore_indices` (exact captured-index set) and adds
`sequence_witness_checked`, the production instantiation of the sequence
theorem; the Step 3 dependency map is `proofs/top_down/interface-inventory.md`.
The following checkpoint exports the `EClasses` component contents (entries,
reprs, uses, minimum pool: views at the token's frame and archive prefixes)
through `restore`/`try_restore`, closing the derived-contract audit table.
The final checkpoint removes the last execution-first `Vec` marker
(`try_mark_adaptive`, now checked from `mark_with_options` and
`runtime_apply_adaptive`) and carries the benchmark-driven constant-factor
fixes (pre-sized dedupe buffers). Trust: 50 default + 5 literal (CI
`EXPECTED_DEFAULT=50`).

## Next actions (goal extended by the user on 2026-09-16, evening)

1. Done (`45fc132`): the protocol report for `f304bc7`.
2. Caching / destination-passing work (from the allocation tour). Done: the
   Trail→Hot dedupe `HashSet` owned by the `Vec` (`987a964`); the `SpMap`
   restore unwinding its index over the discarded suffix through a
   previous-occurrence column instead of rebuilding from the survivors
   (`54563da`; the fingerprint-bucket variant was dropped because vstd
   specifies no `hash_one`, so it would have added trust). Settled by
   inspection, no change: `diff_compress::sort_frame_by_index`'s copy is
   reached only from the cold-stack sealing paths (`seal_runs`,
   `seal_runs_dict`), whose sole caller is
   `containers-conformance/tests/cold_stack_differential.rs`, and from the
   legacy compression cadence (`compress_frame`, `CompressionMode` other
   than `None`) that production does not enable; no production path pays the
   copy. Done: `HintedArena::note_hint` pushes into its bucket through two
   `core::mem::swap`s against an empty vector instead of copying the bucket
   (no consumer today; vstd specifies `core::mem::swap` and `&mut vec[i]`).
3. Done: store policy for every composite (`doc/design/18-store-policy.md`):
   `TaggedFamily`/`PlainFamily` with `HotFirst` (the default, today's
   choices) and `TrailFirst`; `P = HotFirst` on `UnionFind`, `SparseSet`,
   `CircularList`, `ListArena`, `BPlusTreeSet`, `EClasses`, plus
   `DiffStore::lemma_wf_data_len` for the abstract store's length bound.
4. E-graph: an `EGraphConfig` associated store for the caches; remove the four
   `VecD` sites and the `env_diff_store_kind` lever (≈2.5× dispatch cost).
   Guidance from the traces: Hot-first (VecI/VecP) for equality saturation,
   VecT for SMT-style mark/backtrack use.
5. Final audits (trust ledger is current; partial-API discrepancy is the
   baseline 40 unlisted functions) and the final handoff report, re-running
   the affected benchmarks after each performance change.

## Existing proof architecture to reuse

`vec.rs` uses physical saved maps, saved lengths, ghost snapshots, and existing
canonical `full_trail`/`trail_frames`. No additional persistent history is needed
for reconstruction. Freeze a local `let ghost pre = *self` for replay and separate
buffer reconstruction from final invariant restoration.

Already checked:
- General capture, set, push/regrowth, and pop under the general invariant.
- All-tier restore, including zero depth, mixed retained history, Hot-to-Trail,
  and Cold-to-Hot/Trail reopening. Restore exports exact snapshot/depth/prefix.
- General `open_mark_checked`, with actual DiffStore mark preparation and physical
  frame preservation, and explicit-Defer mark execution.
- `cold_encode::append_sorted` and direct `cold_decode` primitives.
- Exact Trail payload publication, source retirement and frame-partition repair.

Important helpers still in use:
- `discard_prefix_checked`: `copy_within` plus `truncate`, exact bulk retained suffix.
- `retire_trail_prefix_checked`, `retire_hot_prefix_checked`: exact rebased survivors.
- `trail_plan_prefix` and the `lemma_trail_*` preservation lemmas, now over
  `Seq<Seq<(T, I)>>` ghost plans of pool subranges; `lemma_trail_migration_frames`
  and `lemma_trail_migration_wf` recover `wf` after a matched migration.
- `lemma_frame_inv_range_same_saved_map`: transfers reconstruction/domain bounds.
- `append_cold_sorted_checked` and the `lemma_cold_append_*` lemmas: exact Cold
  frame formation from a strictly sorted unique slice (`cold_encode::run_prefix`).

Mark configured/forced fallbacks are checked (`runtime_apply_configured_rollover`,
`runtime_rollover_on_mark`, `runtime_push_frame_fallback`). Never add assumed
postconditions anywhere; decompose instead.

## Broader remaining scope and audit caveats

Derived work includes SparseSet, CircularList, ListArena, UnionFind, BPlusTreeSet,
EClasses, SpMap, AppendOnlyVec, shared-history/group wrappers, actual parallel
fan-out, pending-restore consumers, and relevant supporting structures such as
DenseSpanMap. Review `proofs/top_down/derived-contract-audit.md`; exact component
archive/depth contracts and error framing matter, not just primary contents.

Current trust inventory: **50 default + 5 literal external_body** (CI
`EXPECTED_DEFAULT=50`; the session started at 74 + 5); default axioms are the
hasher axioms plus the per-index-type `obeys_key_model` axioms
(`axiom_key_model_*`), and the one trusted std contract is
`std_sort::sort_pairs_by_index`. Reaudit on final source, and do not mislabel
semantic fallbacks as allocator/diagnostic trust.

Known partial-API CI discrepancy remains open: 73 partial public APIs, 33 allowed,
40 unlisted, zero unsafe-public at the baseline. Review contracts/exposure instead
of bulk allowlisting. Do not claim all CI passes while this remains.

No final conformance benchmarks have run and no parity claim is justified.
Follow `doc/tasks/conformance-performance-inventory.md` and the acceptance protocol:
fix tolerance/decision rule before evaluating results, repeat matched workloads on
the same hardware/toolchain/features, retain raw Criterion estimates/CIs, require
all applicable cases to bound slowdown within tolerance, and fix regressions.
Inconclusive results remain open. Unmatched tier operations compare against
`d191c4a` separately and do not establish legacy parity. Include parallel coverage
or document and resolve required coverage gaps. Avoid verifier/test load while
benchmarking.

Additional final gates include consumer tests:
`cargo test -p semi-persistent-egraph -p semi-persistent-satcore`.
The checklist is authoritative for the complete required gate inventory.

## Navigation

All paths below are relative to the repository:
- `containers-verus/doc/tasks/nightshift-completion-goal.md`
- `containers-verus/doc/tasks/semi-persistence-completion-goal.md`
- `containers-verus/doc/tasks/all-tier-semi-persistence-goal.md`
- `containers-verus/doc/tasks/three-tier-top-down-proof-engineering.md`
- `containers-verus/doc/tasks/three-tier-proof-progress.md`
- `containers-verus/proofs/top_down/proof-classification.md`
- `containers-verus/proofs/top_down/derived-contract-audit.md`
- `containers-verus/proofs/top_down/composition.rs`

The work is making progress, but all four acceptance milestones are not yet
closed. Preserve that scope and report unresolved obligations candidly.

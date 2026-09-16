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
- Branch: `d21-exec`
- HEAD: `9617902` — `Prove full Trail migration preservation for matched plans`
- Last observed local tracking status: ahead of `origin/d21-exec` by 33 commits
  (local ref comparison, not a new remote fetch).
- The current selection work is **uncommitted**. Preserve it.

At HEAD, default and literal-types each passed **2457 verified, zero errors**;
conditional composition passed **80 verified, zero errors**. Evidence:
`/tmp/sp-d21-trail-wf-default.log`, `...-literal.log`, `...-composition.log`.
The previous runtime checkpoint had 277 feature tests passing, 10 ignored,
and four release policy-matrix tests passing. Do not confuse those with the
current uncommitted source's results.

## Current uncommitted work

Modified:
- `containers-verus/src/lib.rs`: registers private module `trail_select`.
- `containers-verus/src/vec.rs`: both Trail key builders now call checked
  `trail_select::build_keys`; ordinary migration's group-selection loop now calls
  checked `trail_select::select_positions`.
- `containers-verus/doc/tasks/three-tier-proof-progress.md`: new producer section.
- `containers-verus/proofs/top_down/proof-classification.md`: reuse/remaining-gap note.

New:
- `containers-verus/src/trail_select.rs` (untracked until added).
- This handoff file.

The new module contains:

- `keyed_source(entries, keys)`: exact length, each key names a valid physical source
  position with the matching index, and every source position occurs.
- `keys_sorted(keys)`: lexicographic order on `(index, chronological position)`.
- `build_keys`: checked reserved linear loop, exporting exact keys and correspondence.
- `group_positions(keys,n)`: recursive mathematical result of scanning group heads.
  This is a spec sequence, not a runtime or persistent ghost buffer.
- `select_positions`: checked actual linear scan; exports exactly `group_positions`.
- `lemma_group_first`: a sorted group head names the earliest source capture.
- `lemma_selected_first`: all selected positions are valid earliest captures.
- `lemma_selected_covers`: every input index has a retained group head.
- `lemma_keyed_permutation`: multiset equality preserves source correspondence.

Targeted verification: **9 verified, zero errors** in
`/tmp/sp-d21-trail-select5.log`.
Full default verification of this source: **2466 verified, zero errors** in
`/tmp/sp-d21-select-default.log` (finished in 3m38s). Literal-types also passed
**2466 verified, zero errors**, in `/tmp/sp-d21-select-literal.log` (3m46s).
Conditional composition passed **80 verified, zero errors** in
`/tmp/sp-d21-select-composition.log`.
Formatting/whitespace and unchanged-legacy checks passed before the latest prose
handoff addition. No trust was introduced or removed by this extraction.

**Limits:** `sort_unstable` still has no checked semantic contract in the pinned
vstd. The new lemmas explicitly require sortedness/permutation; no caller may
assume those facts. Selected-payload uniqueness, full map equality, chronological
reordering, and adaptive deduplication still need proof. Surrounding migration
and planner bodies remain external until their real dependencies verify.

Runtime shape remains the same buffers and sorting calls, with one reserved
linear key-building loop and the existing linear group scan. Performance parity
has NOT been measured. Do not substitute the existing quadratic insertion sort
for the current sorting implementation merely to obtain a proof.

## Validation at handoff creation (resolved)

A sequential `set -e` shell was launched through Codex exec session **99198**.
Default and literal-types verification both finished successfully, and
composition passed (80 verified, zero errors). That shell was killed with the
Codex session while the feature suite was running (its log stopped before
`eclasses_behavior` reported), so the feature suite and the policy matrix were
rerun from scratch afterwards: **277 passed, 10 ignored** and **4 passed**
(`/tmp/sp-d21-select-tests.log`, `/tmp/sp-d21-select-policy.log`). Formatting,
whitespace and the unchanged-legacy check also passed on this source. The
original queue was:

```sh
cargo fmt --all
touch containers-verus/src/trail_select.rs
cargo verus verify -p semi-persistent-containers-verus -- --time-expanded > /tmp/sp-d21-select-default.log 2>&1
touch containers-verus/src/trail_select.rs
cargo verus verify -p semi-persistent-containers-verus --features literal-types -- --time-expanded > /tmp/sp-d21-select-literal.log 2>&1
verus --crate-type lib containers-verus/proofs/top_down/composition.rs > /tmp/sp-d21-select-composition.log 2>&1
cargo test -p semi-persistent-containers-verus --features 'compat-all,literal-types' > /tmp/sp-d21-select-tests.log 2>&1
PROPTEST_CASES=1024 cargo test -p containers-conformance --release --test three_tier_policy_matrix > /tmp/sp-d21-select-policy.log 2>&1
cargo fmt --all -- --check
git diff --check
git diff --quiet d191c4a -- containers
```

Codex session handles may not transfer to Claude. Inspect terminal log endings
and actual process state before starting anything duplicate. Missing later logs
can simply mean earlier checks have not finished. Because this uses `set -e`, an
error stops subsequent checks. An observation timeout is not a terminal result.
Do not edit sources while these checks are still measuring this revision.

Pinned tools: Verus `0.2026.08.02.b677dd5`, Rust `1.97.1`, vstd `2026-08-02`,
macOS aarch64. cargo-verus can cache across changed verifier flags; touch a source
before switching flags when there was no source change. Full checks take several
minutes. Capture terminal results, not just partial log text.

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

Important Trail helpers:
- `append_selected_hot_frame_checked`: ordinary selected-position copy loop.
- `append_owned_hot_frame_checked`: adaptive owned bulk `Vec::append`, empties
  the source payload. The planner drops these payloads immediately afterward.
- `append_trail_plan_checked`: exact concatenation, header offsets and saved lengths.
- `discard_prefix_checked`: `copy_within` plus `truncate`, exact bulk retained suffix.
- `retire_trail_prefix_checked`, `retire_hot_prefix_checked`: exact rebased survivors.
- `execute_trail_plan_storage_checked`: actual append plus retirement and exact
  physical effects. **Full wf is conditional on `pre.trail_plan_matches(plan)`.**
- `trail_plan_matches`: each payload unique, with full optional saved-map equality
  to its source Trail frame, including absence. This is a producer obligation.
- `lemma_frame_inv_range_same_saved_map`: transfers reconstruction/domain bounds.
- `lemma_trail_plan_contract_at`, `lemma_trail_moved_frame`: matched payload meaning
  transfers to the actual destination range.
- `lemma_trail_retained_frame`, `lemma_trail_old_hot_frame`, fixed-history/ingress/
  representation lemmas, and `lemma_wf_from_named_parts`: recover the original wf.

`runtime_execute_trail_plan` still being external is intentional unfinished work:
the actual planner must prove `trail_plan_matches` before semantic trust can go.
Mark configured/forced fallbacks similarly remain open because actual rollover
preservation is unfinished. Never add assumed postconditions to discharge them.

## Next actions

1. Resolve the in-flight gate results and update progress evidence. If they pass,
   review and commit this selection checkpoint locally with signing; do not push.
2. Finish the selection producer: prove unique selected indices and exact optional
   saved-map equality, including absence; prove chronological permutation preserves
   the unique map; connect ordinary and adaptive producers to the storage contract.
3. Discharge actual sorting while preserving the required performance profile and
   avoiding new trust. Keep its separate sortedness and permutation interfaces.
4. Finish Hot-to-Cold semantic assembly/retirement and actual legal policy selection
   and execution. Connect configured/forced/adaptive/mark dispatch to checked effects.
5. Instantiate production sequence composition, then close the full derived/group
   scope and final audit/benchmark gates. Do not stop at Vec.

## Broader remaining scope and audit caveats

Derived work includes SparseSet, CircularList, ListArena, UnionFind, BPlusTreeSet,
EClasses, SpMap, AppendOnlyVec, shared-history/group wrappers, actual parallel
fan-out, pending-restore consumers, and relevant supporting structures such as
DenseSpanMap. Review `proofs/top_down/derived-contract-audit.md`; exact component
archive/depth contracts and error framing matter, not just primary contents.

Last documented trust inventory: **74 default + 5 literal external_body**
(default: four opaque structs and 70 functions); axioms unchanged at one default
plus five literal. The selection patch contains no new trust. Reaudit on final
source, and do not mislabel semantic fallbacks as allocator/diagnostic trust.

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

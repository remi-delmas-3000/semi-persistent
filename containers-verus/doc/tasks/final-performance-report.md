# Final performance validation report

Required completion gate from
[semi-persistence-completion-goal.md](semi-persistence-completion-goal.md)
(protocol steps 1–5), applied to the final verified revision. The target
inventory is [conformance-performance-inventory.md](conformance-performance-inventory.md);
this report rechecks it against the final source and records measurements.

## Protocol (fixed 2026-09-16, before any timing run)

Environment: Apple M4 Pro (14 cores), 48 GB, macOS 27.0, rustc/cargo 1.97.1
(`8bab26f4f 2026-07-14`), release profile, `SEMPER_COMPRESS` and `SEMPER_DIFF`
unset, no concurrent verifier or test load (the Verus/test gate battery is run
to completion before the first timing command, and nothing else is started
until the last one finishes). Benchmark sources
(`containers-conformance/benches/*`, `containers-conformance/src`,
`containers-conformance/Cargo.toml`) are byte-identical to checkpoint
`d191c4a`, so both revisions run the same benchmark code and differ only in the
verified crate.

Targets and roles (rechecked on the final source; the inventory's
classification stands):

| Target | Paired cases (same binary) | Role |
|---|---|---|
| `tracked_vec_bench` | `tracked_veci/mark_churn/{prod,verus}/N`, `tracked_vecp/mark_churn/{prod,verus}/N` | Required legacy comparison |
| `nested_mark_bench` | `nested_mark/vecp_deep_history/{prod,verus}/depth` | Required legacy comparison |
| `retained_containers_bench` | 13 groups × `{legacy,verified}` (vec, list, class_ring, map, sparse_set, aov) | Required legacy comparison |
| `eclasses_bench` | `eclasses/{merge_cascade,find_sweep,mark_merge_restore}/{retained,verified}/N` | Required legacy comparison |
| `bplus_cursor_bitset_bench` | 6 groups × `{prod,verus}` | Required legacy comparison |
| `three_tier_bench` | `three_tier/write/*/{profile}` vs `production`; `three_tier/mark/no_rollover_smt` vs `no_rollover_production`; `three_tier/restore/*_one_frame` vs `production_one_frame`; `three_tier/end_to_end/{smt_backtrack,eqsat_retained}` vs `*_production`; `three_tier_v1/write/*/{dyn_*,static_*}` vs `production_veci`/`production_vecp` | Workload controls (legacy has no explicit tier policy; differences labelled) |
| `three_tier_bench` tier-specific | `three_tier/mark/{trail_to_hot,hot_to_cold,explicit_defer_smt}`, `three_tier/restore/{trail,hot,cold}_one_frame`, `all_tiers_deep`, `three_tier/conversion/{trail_to_hot_dedupe,hot_to_cold_runs}`, `three_tier/promotion/cold_survivor_write_restore`, `three_tier/adaptive_decision/*`, `three_tier_v1/rollover/*`, `three_tier_v1/promotion/*`, `three_tier_v1/restore/*` | No legacy equivalent: compared with checkpoint `d191c4a` (supplementary; cannot establish legacy parity) |
| `diff_compress_bench`, `two_stack_bench`, `reorder_bench`, `scheme_comparison_bench`, `parallel_frame_bench`, `eager_write_bench`, `normalize_bench` | none | Supplementary or single-implementation; not parity evidence (recorded as exclusions) |

Coverage gaps carried from the inventory: the parallel-frame target measures
encoder fan-out, not group restore, and no legacy group-restore benchmark
exists (`ForkHistory::mark_parallel`/`restore_parallel` have no legacy
counterpart); the eager-write target does not call either container. Both are
reported as gaps, not measured as parity.

Noise tolerance and decision rule (from the project's existing benchmark
policy: the 5–8 % same-code noise band established in
`three-tier-e5-measurement-a414090.md`; this rule is not widened after seeing
results):

1. Tolerance `τ = 1.08` on the ratio of mean times `r = verified / legacy`
   (or `final / d191c4a` for the checkpoint comparison).
2. Every case is measured in two independent full runs (run A, run B) of its
   target. For each run the ratio interval is the conservative quotient of
   Criterion's 95 % mean confidence intervals, `[v_lo / l_hi, v_hi / l_lo]`.
3. Status per paired case: **pass** when the ratio's upper bound is `≤ τ` in
   both runs; **regression** when the ratio's lower bound is `> τ` in both
   runs; otherwise **inconclusive**, which triggers a third, longer run of that
   case alone (`--sample-size 100 --warm-up-time 3 --measurement-time 10`);
   after the rerun the case is pass/regression by the rerun's interval alone
   if it is decisive, otherwise it stays inconclusive and is reported as open.
4. Repeatability calibration precedes evaluation: the same-code drift of the
   legacy rows between run A and run B must stay inside the band (point
   estimates within 8 %); a run pair with legacy drift beyond that is
   discarded and repeated, because it indicates machine noise rather than a
   code effect.
5. Criterion settings: each target's registered configuration, except
   `three_tier_bench`, whose registered `sample_size(10)`/250 ms/500 ms are too
   coarse to bound an 8 % effect; it runs with
   `--sample-size 30 --warm-up-time 2 --measurement-time 5` on both revisions.
6. Every applicable paired case must pass. Aggregate improvements do not
   offset an individual regression. A reproducible regression is investigated
   and fixed without weakening proofs or touching `containers/`, then the
   affected correctness gates and benchmarks are rerun.

Commands (from the repository root; `<name>` is the target):

```
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench <name> -- --save-baseline runA
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench <name> -- --save-baseline runB
```

Checkpoint comparison: a git worktree at `d191c4a`
(`/Users/remidelmas/projects/sp-d21-d191c4a`, its own build directory) runs
`three_tier_bench` with the same settings under `--save-baseline d191c4a_A` /
`d191c4a_B`; both trees write to one `CRITERION_HOME`
(`<final tree>/target/criterion`), and the final tree's `runA`/`runB`
baselines are compared to the checkpoint ones by the same rule. Runs are
interleaved (A final, A checkpoint, B final, B checkpoint) so slow machine
drift affects both sides alike; bench binaries are built before the first
timing command so no compilation overlaps a measurement.

Raw artifacts: `target/criterion/**/{runA,runB,d191c4a_A,d191c4a_B}/estimates.json`
plus the full Criterion logs under `/tmp/sp-d21-bench-*.log`; the comparison
tables below are generated from the `estimates.json` files by
`containers-verus/tools/bench_compare.py` (ratio, interval, status).

## Preliminary run and regression investigation (2026-09-16, revision `09f00b0`)

The first execution of the protocol was stopped after run A of every target
plus the checkpoint's `three_tier_bench` run A, because run A already showed
reproducible regressions (intervals of ±0.5 % or tighter) that had to be fixed
before a final two-run evaluation could mean anything. Everything measured is
retained under baselines `runA`, `d191c4a_A` and the partial `runB`
(`tracked_vec_bench` only); the paired targets were additionally run once at
the checkpoint (`d191c4a_A`) so each legacy gap could be classified as
pre-existing or introduced by this branch.

Findings, per case class:

1. **Introduced by this branch, adaptive Trail dedupe (fixed).**
   `three_tier_v2/adaptive/singleton_W512_U512_R512/budget_4096/dyn_trail`
   ×7.0, `three_tier_v2/adaptive/unique_W512_U512_R1/budget_4096/dyn_trail`
   ×1.09 and `three_tier/adaptive_decision/low_duplicates_no_convert/512`
   ×1.09 against the checkpoint. Cause: `dedupe_trail_range` inserted into a
   `HashSet` created empty (`HashSet::default()`) for every pass, so a
   512-entry frame paid ~9 rehashes. Fix: `seen.reserve(end - start)` and
   `out.reserve(end - start)` at the start of the pass (vstd-specified,
   view-preserving). After the fix the two shuffled-order cases run at 2.14 µs
   against the checkpoint's 9.16 µs (ratio 0.23 — the old pass sorted a
   scratch copy), and the ascending-order singleton case at 1.76 µs against
   1.35 µs (ratio 1.31): pdqsort is O(n) on already-sorted input while the
   hash pass is order-blind. That residual is inherent to the index-set
   dedupe chosen for this branch and is reported as such below.
2. **Introduced by this branch, closed-history byte fold.**
   `three_tier_v2/large/W64_U16_R1_frames256/budget_unbounded/dyn_inline`
   ×1.16–1.19 and `dyn_parallel` ×1.10 against the checkpoint (154 ns → ~180
   ns on the adaptive early-return path). The checked fold reads each frame
   through `pair_frame_entries` inside a `while` loop with a runtime bounds
   check per frame where the old code folded over a slice. The disassembly of
   the `DynStore<u64, usize>` instantiation showed the difference exactly: the
   checkpoint's loop is seven instructions with one counter, the checked
   loop carried a second down-counter for the index bound (an explicit
   `min(closed, len)` bound did not remove it — LLVM kept both counters).
   Fix: fold over the whole stack, whose length is the loop bound, and take
   the open frame's entries back out once (`checked_sub`, refusing on
   underflow like the additions); same counts, same checked arithmetic. After
   the fix: `dyn_inline` 156 ns vs 154 ns (ratio 1.01) and `dyn_parallel`
   148 ns vs 156 ns (0.95), both pass. A forced-alignment build of the
   pre-fix source had left both at ×1.17–1.18, confirming this one was not
   layout.
3. **Introduced by this branch, code layout only.**
   `eclasses/find_sweep/verified/4096` (×1.43 vs legacy, 1.00 at the
   checkpoint) and `tracked_vecp/mark_churn/verus/1000000` (×1.10 vs legacy,
   1.03 at the checkpoint). Bisected by commit: the find sweep is clean at
   `a831cc1` and regressed at `9df28cb`; the mark churn is clean at `990eb08`
   (1.02) and regressed at `a831cc1` (1.10). Neither interval changes any
   function on the measured path (`find_const` → `get_index` → store read;
   `try_mark` → Hot-defer mark → `set_index` → `try_restore`): the commits
   change specs, migration/adaptive code and marker attributes only, and the
   bodies of the mark-path fallbacks are textually identical before and
   after. Controlled test: the same source built with
   `-C llvm-args=-align-all-functions=6 -C llvm-args=-align-all-nofallthru-blocks=5`
   (separate target directory, everything else identical) measures the
   find sweep at 221.7 µs verified vs 252.2 µs retained (ratio 0.88) and the
   mark churn at 1.240 ms vs 1.221 ms (1.015): both pass, and the *legacy*
   arms moved as much as the verified ones (retained find sweep 212 → 252
   µs). Code placement, not work, explains these two cases. No source change
   is made for them; the default-build numbers are reported as measured with
   this control beside them.
4. **Pre-existing against legacy (unchanged by this branch).**
   `bplus/from_sorted_then_scan/verus` ×1.90 and `bplus/insert_shuffled/verus`
   ×1.12–1.13 are identical at `d191c4a`; `aov/log/verified` is ×1.08–1.11
   with a wide interval at both revisions (inconclusive). The B+ tree and
   append-only vector were not touched by this branch.
5. **Workload controls, pre-existing.** The `three_tier/*` and
   `three_tier_v1/*` verified-versus-production rows exceed the tolerance by
   ×1.1–×6.7 at both revisions (the checkpoint comparison of the same ids is
   ≤1.08 except the cases in items 1–2). These production arms are workload
   controls, not equivalent operations: the production `Vec` has no Trail
   tier, no tier policy and no adaptive pass, so they measure the cost of the
   three-tier design itself, as the inventory anticipated. They are reported
   with their ratios; they are not evidence about this branch's proof work.

`three_tier_v1/restore/deep_64_frames/dyn_trail` (×1.11 in run A) measured
1.01 on the rebuilt binary with no change to its code path; it is treated as a
run-to-run layout/noise effect and re-evaluated in the final two-run
protocol like every other case.

## Results

(final two-run evaluation to be appended)

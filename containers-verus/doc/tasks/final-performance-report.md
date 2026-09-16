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

Checkpoint comparison: a git worktree at `d191c4a` shares the workspace
`target/` directory (`CARGO_TARGET_DIR`), runs `three_tier_bench` with the same
settings under `--save-baseline d191c4a_A` / `d191c4a_B`, and the final tree's
`runA`/`runB` baselines are compared to them by the same rule.

Raw artifacts: `target/criterion/**/{runA,runB,d191c4a_A,d191c4a_B}/estimates.json`
plus the full Criterion logs under `/tmp/sp-d21-bench-*.log`; the comparison
tables below are generated from the `estimates.json` files by
`containers-verus/tools/bench_compare.py` (ratio, interval, status).

## Results

(to be appended after the timing runs)

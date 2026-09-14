# Nightshift goal: DiffStore-owned three-tier protocol and adaptive large-egraph study

Continue from the current uncommitted working tree on branch `d21-exec` at
`a414090`; do not reset or discard the existing three-tier work. Use
`containers-verus/doc/tasks/three-tier-frame-architecture-goal.md` and
`containers-verus/doc/tasks/three-tier-e5-measurement-a414090.md` as the source
of truth.

Complete and validate the DiffStore-owned three-tier architecture. `DiffStore`
must be the only ingress-protocol abstraction: `InlineStore` and
`ParallelStore` statically implement first-capture-wins and write directly to
Hot; `TrailStore` appends duplicate-preserving chronological writes to Trail;
`DynStore` selects Inline, Parallel, or Trail at runtime so identical workloads
can measure all protocols without recompilation. `Vec` must not contain a
second `CaptureMode` field, const strategy, or conflicting dispatch abstraction.
Rollover policy remains independent of `DiffStore` and controls only when closed
history transitions Trail → Hot → Cold.

First finish the current refactor and run all required checks: formatting,
focused three-tier tests, default and `compat-all,literal-types`
containers-verus suites, the 1,024-case release policy matrix, full release
containers-conformance, and the egraph consumer suite. Preserve all APIs that
existed at `a414090`, preserve `VecD`'s historical concrete type, keep
`containers/` unchanged as the independent oracle, do not create a commit, and
do not begin proof implementation. Fix any failures before proceeding.

Then rerun the exact VecP 1K/1M and aggregate guard benchmarks against
`pre_three_tier_a414090`. Confirm that deriving ingress from the concrete
`DiffStore` preserves the recovered zero-regression VecP hot path: static
VecP/VecI writes must compile directly to first-capture capture with no runtime
mode branch, VecT writes directly to Trail, and only `DynStore` performs runtime
protocol dispatch. Retain same-process production controls and report confidence
intervals, not point estimates alone.

Extend the benchmark campaign to compare `DynStore` `StoreKind::Inline`,
`StoreKind::Parallel`, and `StoreKind::Trail` on identical deterministic
workloads. Measure at minimum:

- write throughput at low and high duplicate density;
- shallow mark/restore and deep backtracking;
- Trail restore before rollover;
- Trail → Hot dedupe formation cost and memory reduction;
- Hot restore versus Trail restore;
- Hot → Cold sort/run-construction cost and retained-memory reduction;
- direct Cold run restore;
- promotion followed by additional writes and another restore;
- complete SMT-style backtracking traces;
- equality-saturation and EClasses mark/merge/restore traces;
- large retained-history traces representative of very large egraphs;
- logical bytes per tier, allocated capacity, and transient peak scratch.

Study an adaptive large-egraph policy using the cost model `W` writes → `U`
unique cells → `R` contiguous runs:

- Trail has negligible frame-formation work but restores `W` entries.
- Hot pays dedupe once and restores `U` unique entries.
- Cold pays sorting/run construction and restores `R` vectorized slices.
- Trail → Hot should be considered when duplicate or retained-byte overhead
  makes `W/U` sufficiently large.
- Hot → Cold should be considered when memory pressure is real and `U/R`
  indicates enough locality for run copies; singleton-heavy frames must remain
  Hot unless an explicit memory budget accepts the restore tradeoff.
- All automatic decisions must use deterministic recorded statistics and
  explicit memory-budget inputs, not ambient allocator state.
- Rollover operates only on closed oldest prefixes and never migrates the newly
  opened frame.

Use the existing per-mark control:

- `RolloverPolicy::Defer` seals/opens without conversion.
- `RolloverPolicy::ApplyConfigured` enforces retained tier limits.
- `RolloverPolicy::ForceClosed` independently forces Trail → Hot, Hot → Cold,
  or both, with Trail → Hot executed first.
- `ShrinkPolicy` remains capacity reclamation and must not be overloaded with
  representation migration.

Measure the explicit directive overhead and preserve the source-compatible
`try_mark(ShrinkPolicy)` path.

Distinguish two adaptive questions:

1. **Required first target:** continue using `TrailStore` for new writes while
   adaptively converting closed Trail frames to Hot and Cold. This changes
   historical representation without changing the live `DiffStore` protocol.
2. **Optional research target:** determine whether a live `DynStore` can safely
   switch future ingress from Trail to first-capture-wins at a mark boundary.
   Do not implement this casually. A safe switch would require closing the
   Trail frame, migrating or preserving all older representations, converting
   the live backend and capture state without changing values, opening a fresh
   unique frame, and proving through differential runtime tests that token,
   restore, and failure semantics remain unchanged. If those requirements or
   measurements do not justify it, document the design and leave live protocol
   switching unimplemented.

Add focused deterministic regressions and a `PROPTEST_CASES`-aware differential
matrix for every implemented adaptive transition. Include empty frames,
duplicate-heavy frames, finite and unbounded retention, nonmonotone saved
lengths, restore targets in every populated tier, forced/deferred rollover,
memory-pressure transitions, write-after-promotion, and deep unwind. Compare
values, length, depth, token liveness, rejected operations, and tier ownership
after every operation.

Optimize only from measured end-to-end evidence. Do not reintroduce dual stack
meanings, runtime dispatch into static VecP/VecI/VecT writes, pair decoding on
the Cold restore path, or orphan payloads. Revert experiments that improve one
microbenchmark while materially regressing another required workload. Record
accepted and rejected experiments with exact commands and confidence intervals.

Stop only when:

- all runtime and differential gates are green;
- static VecP/VecI/VecT paths retain their intended zero-overhead `DiffStore`
  dispatch;
- DynStore Inline/Parallel/Trail comparisons are recorded;
- the adaptive large-egraph policy has measured thresholds or a documented
  negative result;
- peak and retained memory evidence is recorded;
- the final diff contains no `containers/` or proof changes;
- the architecture and measurement documents accurately distinguish built
  behavior, measured behavior, optional research, and deferred proof work.

If blocked, preserve the smallest failing trace, exact command/output, and a
precise architectural explanation rather than weakening the representation
boundaries or silently changing compatibility behavior.

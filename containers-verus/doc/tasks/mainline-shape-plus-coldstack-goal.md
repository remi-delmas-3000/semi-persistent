# Mainline's container plus a cold stack

The finding that resets the architecture (2026-09-12): the mainline verified
container never had a diff-log type. It carries production's fields verbatim
(`containers-verus/src/vec.rs:647` at `56a06a5`):

    diff_log: std::vec::Vec<(T, I)>,
    frames:   std::vec::Vec<Frame<I>>,

The `DiffLog` enum - `Cols`, the split columns, `Adaptive`, every wrapper -
was introduced by the compression branch itself, and the 5.7x restore
regression plus the residual mark_churn tax were the price of that type, not
of compression. The design is therefore not a redesign: it is mainline's
container unchanged, plus one cold stack beside it.

## Layout (verbatim, the lock target - ruled 2026-09-13)

    struct Vec<T, I, S> {
        store: S,                          // live values Vec<T> + capture discipline

        hot_value_pool: Vec<(T, I)>,       // all uncompressed diffs
        hot_stack: Vec<HotFrame<I>>,       // { saved_len, start, end } into hot_value_pool

        cold_value_pool: Vec<T>,           // all value runs, concatenated
        cold_index_runs: Vec<IndexRun<I>>, // { base, start, len }: run lands at
                                           //   live[base..], values at
                                           //   cold_value_pool[start..start+len]
        cold_stack: Vec<ColdFrame<I>>,     // { runs_start, runs_len, saved_len }
    }

Cold frames are the oldest [0, k), hot frames the most recent [k, n);
depth n = cold_stack.len() + hot_stack.len(). A token's frame_idx resolves
by comparison with the split point; each tier's header carries saved_len.
No unified frame array, no loc tag, no CSR offs column (IndexRun carries
its own len), no dict or plain cold modes in v1 - every cold frame is runs.

## Algorithms (ruled)

- Capture: unique stores check the flag per write; the trail store appends
  unconditionally and its flag hooks are no-ops. Both push into
  hot_value_pool.
- mark(reclaim_policy, compress: bool): push HotFrame{saved_len, start=end
  =pool.len()}; when compress, run the compression pass; reclaim per policy.
- Compression pass (all hot frames migrate, oldest first, IN PLACE in the
  pool slice [start, end) - no stratum materialization):
    1. normalize (a DiffStore hook, called only here so mark(_, false)
       stays O(1) for trail): unique discipline = sort_unstable by index
       (no ties, allocation-free); trail = STABLE sort by index (ties keep
       temporal order), then a forward pass compacting the first entry per
       index group; the frame's effective length shrinks to the kept count.
       Extents never shift: the dead tail is reclaimed when the whole pool
       truncates at the end of the pass.
    2. translate: one traversal of pool[start..start+kept] appending values
       to cold_value_pool, opening an IndexRun at each index discontinuity,
       closing with a ColdFrame. A diffless frame still emits its ColdFrame
       (runs_len 0) - frame count is token identity.
    3. after the last frame: hot_stack clears, hot_value_pool truncates to
       0 always; capacity is released only when reclaim_policy asks.
- Restore cold frame: resize live to saved_len, then per run one clamped
  memcpy cold_value_pool[start..start+len] -> live[base..].
- Restore hot frame: reverse walk of pool[start..end] (high to low), so
  the most ancient value lands last - correct for trail duplicates.
- Pop: hot = pop header + truncate pool to its start; cold = pop header +
  truncate cold_index_runs to runs_start and cold_value_pool to the popped
  frame's first run start.

Known honesty note: Rust's stable slice sort uses a transient merge buffer,
so the trail normalize is pool-in-place but not allocation-free during the
sort; the unique branch is. Upgrade (in-place stable merge, or decoration
into the frame's own dead tail) only when a profile shows it.

## Method (exec-first, per the 2026-09-12 direction)

Make it work, make it fast, then prove it: implement on the bare fields,
validate against the conformance differential suite, benchmark against the
mainline baseline (the write path must sit at +-0 by identity; a new
deep-history benchmark times the cold memcpy restore in isolation), LOCK the
algorithm, then re-attach proofs. During the exec phase changed bodies carry
their intended contracts as external_body scaffolding recorded here; the
locked state discharges them, reusing commit 20's proof assets (ColdStack wf
and restores, the dedupe overlay theorem, the fold frame rule) at the two
seams.

## Phases

- A2a: delete the DiffLog type; bare `diff_log` field; compression off;
  every gate green; mark_churn == mainline by identity (measured to confirm).
- A2b: add cold/scratch/loc + mark-driven evict/reclaim + cold restores;
  conformance + trail compression + deep-history bench.
- A3: lock; discharge the scaffolding ledger; full battery.

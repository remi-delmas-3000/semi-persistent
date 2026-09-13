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

## Layout (verbatim, the lock target)

    struct Vec<T, I, S> {
        store:    S,
        diff_log: Vec<(T, I)>,         // mainline's field - the hot tier
        frames:   Vec<Frame<I>>,       // mainline's field; diff_start
                                       //   generalizes to loc: Hot(off) | Cold(idx)
        cold:     ColdStack<T, I, VC>, // doc restore-from-compressed-frames \S3,
                                       //   already built and proven
        scratch:  Vec<T>,              // dict-decode buffer (\S4)
    }

Hot writes and hot restores are mainline's code by identity, so the write
path cannot regress by construction. The cold stack is reachable only from
`mark()` (evict past HOT_BUFFER, reclaim over-committed pools) and from
cold-frame restores.

## Algorithms

- Capture: unique-capture stores check the flag per write; the trail store
  appends every write unconditionally. Both push into `diff_log`.
- mark(saved_len): push Frame{saved_len, loc: Hot(diff_log.len())}; if the
  column is tiered and hot frames exceed HOT_BUFFER, evict the oldest hot
  stratum; if pools are over-committed, reclaim.
- Evict: fold-min in temporal order (keep each cell's chronologically first
  capture; decorate with position, one sort by (index, position), linear
  group-first pass - the sort RLE needs does double duty), select the mode
  per frame with the restore term (\S5), seal into the cold pools, retag the
  frame's loc Hot -> Cold, shift remaining Hot offsets by the deduped delta.
- Restore: hot frame = mainline's backward loop; cold Plain = backward walk
  of the pooled pairs; cold Runs = one clamped copy_from_slice per run; cold
  RunsDict = per-run dict decode into `scratch`, then the same block copy.
- Pop: hot = truncate `diff_log`; cold = truncate every pool to the popped
  header's offsets.

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

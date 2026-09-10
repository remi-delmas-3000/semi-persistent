# Goal: fork-history sharing + parallel adaptive diff compression on the e-graph, measured on Sundance

Branch `spvec-compression` (repo `yaspar-org/semi-persistent`, local `sp-compression`).
This is a transient planning document, discarded once the work lands. The durable design
(current shape and rejected alternatives) lives in the design docs: `doc/design/09`
(compression), `doc/design/10` (fork history), `doc/design/11` (parallel + eager). Every
measured finding from this work is recorded THERE, not here (see G4).

This is a task contract: every acceptance criterion is a command, test, diff, or proof
obligation that either holds or does not; none is discharged by prose. Each deliverable
is labeled BUILT (artifact exists and its own check passes), MEASURED (a number exists,
no artifact), or DESIGNED (a doc exists, no number). A BUILT goal is not discharged by a
MEASURED or DESIGNED result.

## One-line outcome

The e-graph's live mark/restore path compresses every column with a per-column choice of
value-major, index-major (write-order and sorted), or adaptive (`Auto`/calibrated); its
~10 members share ONE fork history; and mark compresses / restore decompresses the
disjoint columns in parallel above a measured threshold. All of it verified, and the
Sundance configuration matrix measured end to end. (BUILT for the code, MEASURED for the
Sundance matrix.)

## Current state this starts from

The compression encoders (value-major with byte + packed codes, index-major write-order
and sorted, the two-stack, the honest `Auto`/calibration selector), the fork-history
reclamation, the shared x1 `History` primitive, and rayon-coexists-with-verus are all
BUILT and verified in `containers-verus`. NONE is on the e-graph's live path:
`EGraph31::mark/restore` (`egraph/src/egraph.rs:2966`) dispatches to ~10 members, each
with a plain `DiffLog`, its own fork history, sequentially. Every phase below is therefore
unbuilt in the e-graph.

## Global invariants (checked at EVERY commit)

- G1. `cargo verus verify -p semi-persistent-containers-verus` prints
  `verification results:: N verified, 0 errors`. A commit with any error count, or with no
  `verification results::` line (a corrupted/incomplete run), is broken and must not exist
  in history.
- G2. `cargo build -p semi-persistent-egraph` and `cargo test -p containers-conformance -p
  semi-persistent-egraph -p semi-persistent-containers-verus` pass (0 failed).
- G3. Every semi-persistence theorem and every fork-reclamation theorem present at the
  start is still present and verified: no `assume`, no `ensures` weakened or removed, no
  theorem downgraded to `external_body`. Check: G1 plus a diff review of the touched
  `ensures`.
- G4. Every measured finding, including negatives, is recorded in the DESIGN docs (09/10/11)
  with the bench/test that regenerates it. This task doc holds raw matrices; the design
  docs hold the durable conclusion.

## Optimal-first clause

Before coding each phase, state the asymptotically and architecturally optimal choice
(data structure, contract shape, borrow structure) and use it. Any downgrade is written
as one line naming the debt and its revival condition, and approved before coding.
"Simpler now, optimal later" is otherwise banned.

## Hard-part-first ordering; phases strictly sequential; no lateral motion

Do the phases in order; within a phase, do the listed items in order (the proof-hardest
first). Do not start a later item, and do not add adjacent or additive work (another
encoder, a refactor, a bench for a not-yet-built path), while the current item is open.
If blocked, stop and state the exact blocker; do not detour into easier work to
manufacture motion. Progress is not reported for a phase until its pinned first item lands
verified.

===============================================================================
## Phase A (BUILT): compression on the live diff-log path, all modes + adaptive

Approach decided (optimal-first), from mapping the proof surface: `Vec` reasons over
`DiffLog@: Seq<(T,I)>` behind a fixed API, and `indices()` (vec.rs:2741/3030/3231) hands
the capture machinery the WHOLE index column as one contiguous `&[I]`. So value-major
(keeps `idxs` whole, preserves flat `@` and `indices()`) integrates with zero `Vec`
re-proof and goes FIRST; index-major (drops `idxs`) needs a capture-machinery change;
sorted (breaks flat `@`) needs the `Vec` multiset model. Cold value column model: a
sequence of IMMUTABLE per-frame `dict`+packed-`Codes` frames plus a plain hot `tail`,
`idxs` kept whole, compacted per frame at mark (amortized O(frame)); packed codes never
need appending. Future "recompress cold" mode (one optimal dictionary across all cold
frames) is noted, not in scope.

- A1 (value-major, the pinned hard item). `cargo verus verify` green (G1) with `DiffLog`
  carrying the two-tier value column (immutable cold frames + hot tail) and a
  `compact_tail` folding a closed frame at mark. Diff review shows `DiffLog`'s public API
  ensures (`@`, `push`, `index`, `subrange_vec`, `drop_front`, `truncate`, `indices`, `wf`)
  UNCHANGED, and `vec.rs` unchanged except the mark-time `compact_tail` call, so no `Vec`
  reconstruction proof was reopened. A conformance test drives a random mark/write/restore
  trace on a `ValueDict` column and asserts the restored `view()` equals the plain oracle's
  (differential); another asserts the column's MEASURED `heap_bytes()` after marks is
  strictly less than plain on a value-repetitive (union-find) workload AND that the cold
  storage is actually dict-coded (not silently plain).
- A2 (index-major write-order). `cargo verus verify` green with the capture machinery no
  longer requiring a contiguous `idxs` slice for compressed columns (the change that lets a
  column drop its index column), and an `IndexRuns` column integrated end to end. Same
  differential test passes; MEASURED `heap_bytes()` < plain on a contiguous-batch workload.
- A3 (sorted index-major). `cargo verus verify` green with `Vec::restore`'s reconstruction
  re-established over the per-frame write-multiset contract (so a reordering flush is sound),
  and an `IndexRunsSorted` column integrated. Differential test (restore == oracle) passes
  on random unique-index traces; MEASURED `heap_bytes()` <= the write-order encoder on a
  shuffled-but-contiguous workload.
- A4 (adaptive). `cargo verus verify` green with `Auto` and `CalibrationPolicy` selecting
  per frame among the INTEGRATED modes at flush, on the live path. A test drives a mixed
  workload and asserts (i) restore == oracle, and (ii) the per-frame encodings chosen match
  `best_mode`'s argmin on the same frames (the selector actually drives the choice, not a
  fixed mode).

Forbidden proxies for Phase A: a computed/projected size for any `heap_bytes()` check; a
`CompressionMode` that silently falls back to plain reported as compression; `external_body`
on any `Vec`/`DiffLog` reconstruction theorem; a standalone encoder test reported as
live-path integration; declaring A2/A3 done while the column still stores a full `idxs`
column (that is value-major, not index-major).

===============================================================================
## Phase B (BUILT): one shared fork history across the e-graph's members

- B1. `cargo verus verify` green (G1) with `EGraph31::mark/restore` routing through ONE
  shared `History` (GenStamps). Diff review shows per-member fork state removed from the
  members that now share, not merely supplemented, and the members mark/restore through the
  genealogy-free `push_frame`/`restore_frame`.
- B2. A test asserts one group token validates the whole group: its generation/depth is a
  single value, not an N-tuple of per-member tokens.
- B3. A test measures peak fork-history bytes (real `heap_bytes` summed over the e-graph) on
  a mark/restore-heavy trace and asserts shared < per-member.
- B4. Branch-cut safety preserved: G1 plus the restore differential test on the shared path
  passes.

Forbidden proxies for Phase B: adding a shared `History` while leaving per-member histories
in place (B1 requires replacement); reporting the already-done container-level reclamation
or the verified-but-unwired `History` primitive as the e-graph wiring.

===============================================================================
## Phase C (BUILT): sequential then parallel mark/restore with concurrent (de)compression

- C1 (sequential baseline). `EGraph31::mark/restore` over the shared history and compressed
  columns: G1 green and the Phase A/B differential traces pass. This is the correct baseline
  the parallel path is checked against.
- C2 (parallel). An `external_body` `_parallel` twin per composite (the e-graph aggregate
  and its sub-aggregates) with a contract IDENTICAL to its sequential method (diff review:
  same `requires`/`ensures`, verbatim), body = `threshold ? rayon fan-out : sequential
  verified path`, so mark compresses and restore decompresses the disjoint columns
  concurrently on the rayon pool above `parallel::PAR_THRESHOLD`.
- C3. A differential test drives random traces through both the sequential and parallel
  mark/restore and asserts identical resulting `view()` for every member.
- C4. A bench shows the parallel path is at least as fast as sequential ABOVE the threshold
  and falls back to sequential below it (never worse than sequential plus a branch). Numbers
  recorded per G4.

Forbidden proxies for Phase C: a `_parallel` twin whose contract is weaker than the
sequential one; `unsafe` in the twin; a twin that never spawns (just calls sequential)
reported as parallel (C4's above-threshold speedup must be real); reporting C4's bench in
place of the C1-C3 verification.

===============================================================================
## Phase D (MEASURED): the Sundance configuration matrix

The adapter exists (`sundance/src/egraphs/semper/mod.rs`, feature `semper-egraph`, EUF-only,
`--arith-solver none`); Sundance pins the semper backend to git rev `ec1eb8ae` (the
`satcore-layer0` base this branch built on). Baseline is `sundance` without semper.

Matrix (each cell one Sundance run):

| axis | settings |
|------|----------|
| compression | off / per-column defaults / all-value-major / all-index-sorted / adaptive |
| fork history | per-member / shared x1 |
| mark/restore | sequential / parallel |

- D1. Sundance's `semper-egraph` dependency repointed at the current branch (diff of
  `sundance/Cargo.toml` shown); `cargo build -p sundance-smt --features semper-egraph`
  succeeds.
- D2. `cargo bench` in Sundance (`benches/lia_benchmarks`, `benches/tableau_benchmarks`, EUF
  subset) runs for baseline and for each matrix cell.
- D3. The matrix is filled with measured solve times and e-graph peak fork bytes, each cell
  naming the bench; the winning configuration and every losing one (with numbers) recorded
  in the design docs (G4). Empty or "expected" cells fail this criterion.
- D4. Every losing configuration is recorded as a negative result with its number, not
  silently dropped.

Forbidden proxies for Phase D: projecting Sundance numbers from the container microbenches;
substituting the local `egraph/benches/saturate_bench` for the Sundance benches; leaving any
matrix cell unmeasured.

## Partial states are failure states

"Wired but the restore theorem not re-proven", "parallel twin added but not
differential-tested", "value-major done, index/sorted/adaptive pending" reported as Phase A
done, "matrix mostly filled" are NOT progress toward done. Each is reported with the exact
remaining obligation and the commit at which it closes. There is no "mostly done": each item
is discharged (its check shown passing) or not discharged (with the one missing thing named).

## Status format for every progress report

For each item: the label BUILT/MEASURED/DESIGNED and the evidence as command output, test
name, diff, or proof result, not a narrative. Example: "A1 BUILT: `cargo verus verify` ->
`1840 verified, 0 errors` (paste); diff shows `DiffLog` API ensures unchanged; differential
test `valuedict_restore_matches_oracle` passes; `heap_bytes` 17KB < 32KB plain." A claim
without its shown check is not discharged.

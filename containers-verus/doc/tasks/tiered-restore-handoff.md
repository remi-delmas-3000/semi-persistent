# Tiered semi-persistent Vec: stores, hot/cold layout, and the conversion theorems

This is a handoff document. It is not a status page: what the code currently
proves is what `cargo verus verify` asserts at `containers-verus`. It explains
the three diff stores, the hot/cold storage layout, the functions that convert
between representations, and the exact theorem each conversion must satisfy. It
points to the mainline design docs and proofs that established the single-stack
mark/restore round trip, which the tiered version reuses as its template.

Everything here is illustrated on one running example: a `VecT<u64, u32>` of
length 10, indices `0..10`, initial value `data[i] == i`.

## 0. The single ghost model (read this first)

There is exactly one abstraction: the **ghost trail** `full_trail: Seq<(T, I)>`
plus per-frame boundaries `trail_frames: Seq<nat>`. The trail records **every
tracked write, duplicates included, in chronological order**, storing the
**old** value (the value that was in the cell just before the write) so that
replaying restores the pre-write state. `snapshots: Seq<Seq<T>>` records the
live vector contents at each mark.

Restore correctness is stated once, against the ghost, in
`spec fn overlay(base, diffs, lo, hi)` (first-entry-wins, front-recursive on
`lo`): overlaying frame `k`'s ghost stratum onto the layer above reconstructs
`snapshots[k]`. The load-bearing lemma is `lemma_cell_eq_overlay` (vec.rs),
the tiered analog of mainline's `lemma_snap_eq_overlay`
(`doc/design/05-flat-central-lemma.md`).

Every physical representation supplies a **commuting equivalence** to the ghost.
That is the whole proof architecture (deliverable D5). The rest of this document
is those equivalences and the functions that realize them.

## 1. The three diff stores

A store owns the live column `data()` and the per-cell capture flags
`captured()`. It differs only in the **capture discipline** and the **replay
protocol**. Two spec fns select behaviour (`src/diff_store.rs`):

| store | `unique_capture_spec()` | `needs_replayed_indices_spec()` | discipline |
|---|---|---|---|
| `TrailStore` (`src/trail_store.rs`) | `false` | `false` | append-always: every write appends `(old, i)` to the log, duplicates included |
| `InlineStore` (`src/inline_store.rs`) | `true` | `true` | first-write-wins; the flag is an inline tag bit on the cell repr, so restore must re-read the replayed indices to clear tags |
| `ParallelStore` (`src/parallel_store.rs`) | `true` | `false` | first-write-wins; the flag is a separate bitmap, wholesale-cleared at restore, so no replayed indices are needed |

"First-write-wins" (unique): the first write to a cell **within a frame** is
captured; later writes to the same cell in the same frame are dropped from the
log (the old value already recorded is the one restore needs). "Append-always"
(trail): no capture check — every write appends, so within-frame duplicates are
the norm.

### Worked example (one frame)

Start: `data = [0,1,2,3,4,5,6,7,8,9]`. `mark()` opens frame 0. Then the writes,
in order: `set(3,30)`, `set(5,50)`, `set(3,31)`, `set(3,32)`, `set(7,70)`.

- **Ghost trail** (frame 0 stratum), old values, all writes:
  `[(3,·old=3), (5,·old=5), (3,·old=31→ wait)]`. Precisely, each entry stores
  the value that was overwritten: `(old=3,idx=3), (old=5,idx=5),
  (old=30,idx=3), (old=31,idx=3), (old=70,idx=7)`. Five entries, duplicates on
  cell 3 included.
- **Trail store** `diff_log`: identical to the ghost stratum — the trail hot
  frame is the **identity embedding** of the ghost. Five entries.
- **Inline / Parallel store** `diff_log`: first-write-wins, so only the first
  capture per cell survives: `(old=3,idx=3), (old=5,idx=5), (old=70,idx=7)`.
  Three entries. This is exactly `dedupe_first` of the ghost stratum.

Restoring frame 0 must return `data` to `[0,1,2,3,4,5,6,7,8,9]` regardless of
store. Trail replays 5 entries right-to-left (later dups are inert under
first-entry-wins overlay); inline/parallel replay 3. Both reconstruct the same
snapshot — that equivalence is `lemma_overlay_dedupe_first`.

## 2. Hot / cold storage layout

Frames live in two stacks (`src/vec.rs`):

- **Hot frames** — recent, uncompressed. `hot_stack: Vec<HotFrame{start,end,
  saved_len}>`; the diff entries live contiguously in `diff_log: Vec<(T,I)>`.
  Hot frame `i` owns `diff_log[hot_stack[i].start .. phys_hot_end(i))`.
- **Cold frames** — older, compressed. `cold_stack: Vec<ColdFrame{runs_start,
  runs_len,saved_len}>`, `cold_index_runs: Vec<Run{base,len,start}>`,
  `cold_value_pool: Vec<T>`. Cold frame `f` owns runs
  `cold_index_runs[runs_start .. runs_start+runs_len)`; each `Run{base,len,
  start}` means "cells `[base, base+len)` take the `len` values at
  `cold_value_pool[start .. start+len)`".

`cold_count = cold_stack.len()` is the tier split: ghost frames `[0, cold_count)`
are cold, `[cold_count, depth)` are hot. `HOT_BUFFER` (8) closed hot frames are
kept before `mark` migrates the oldest to cold.

### Worked example (crossing the tier boundary)

Take the size-10 vector and mark 10 frames, each frame writing a few duplicated
cells (say frame `j` does `set(j%10, 100+j)` three times). After 8 marks the hot
stack holds 8 closed frames in `diff_log`. On the 9th and 10th mark, compression
fires: the oldest hot frame is deduped, then compressed into cold runs, and its
`diff_log` entries are dropped. So after 10 marks you have ~2 cold frames + 8 hot
frames. Frame `j`'s three duplicate writes to cell `j%10` became: 3 trail
entries → 1 deduped entry → 1 cold run of length 1.

## 3. The conversion functions and their theorems

Each conversion must **preserve the write set** (the deduped `(value, index)`
pairs, ≤1 per cell, within the saved region) so that `overlay` still
reconstructs the snapshot. The write set is order-independent (collision-free),
which is why sort and re-encode are free once dedup has run.

### 3a. Right-to-left dedup in place (trail → first-write-wins)

Function: `dedupe_first_spec` (`src/diff_compress.rs`), applied at eviction.
Folds a frame's trail right-to-left keeping the **first** (chronologically
earliest) occurrence per index.

Theorem: **overlay is invariant under dedup** —
`overlay(base, d) == overlay(base, dedupe_first(d))` (`lemma_overlay_dedupe_first`,
vec.rs), because `overlay` is first-entry-wins so later duplicates are inert.
Establishes the write-set invariant: `lemma_dedupe_prefix_props` gives ≤1 entry
per index and subset-of-original.

Example: frame 0's 5 trail entries above dedupe to the 3-entry first-write set.
`overlay` of either onto `[0..10]` yields the same reconstruction.

### 3b. Sort in place (order-independence)

Function: the normalize/sort step that orders a deduped frame by index.

Theorem: **`apply_all == overlay` for a collision-free set** — with ≤1 entry per
index, first-entry-wins never tie-breaks, so any permutation reconstructs the
same snapshot. Carried by `lemma_captured_in_range_dedupe` /
`lemma_frame_inv_range_dedupe` (vec.rs): the captured **set** and the reconstructed
values are preserved under dedupe-and-permute; `frame_cell_inv`'s captured arm
pins each cell by *which* index is present, not *where*.

Example: `[(3,·),(5,·),(7,·)]` sorted is `[(3,·),(5,·),(7,·)]` (already sorted
here); a frame writing `7,3,5` would sort `[(7,·),(3,·),(5,·)] → [(3,·),(5,·),
(7,·)]` with identical reconstruction.

### 3c. Index-run compression (hot → cold)

Function: `compress_all_hot` (`src/vec.rs`, currently external_body, ledgered
with named ensures). Takes the deduped-sorted frame and emits `cold_index_runs`
(maximal consecutive index ranges) + `cold_value_pool`.

Theorem: **`cold_reconstructs(f)`** (the D5 third equivalence), pointwise and
IndexLike-only: for each covered cell `c`, `cold_value(f,c) == snapshots[f][c]`;
for each uncovered saved cell, `snapshots[f][c] == layer_above(f)[c]`. Plus the
structural `repr_ok` (pool partition) and `cold_runs_disjoint` (runs sorted by
base, cell-disjoint — needed so decode/restore windows compose and `cold_value`'s
covering run is unique). Both are `compress_all_hot` ensures.

Example: deduped-sorted cells `{3,5,7}` with values `v3,v5,v7` compress to runs
`[{base:3,len:1,start:0},{base:5,len:1,start:1},{base:7,len:1,start:2}]` and pool
`[v3,v5,v7]`. Consecutive cells `{3,4,5}` would compress to a single run
`{base:3,len:3,start:0}`.

### 3d. Hot → live restore (right-to-left replay)

Function: `restore_hot` (`src/vec.rs`, **fully proven**). Resizes to the target's
saved_len, then `restore_overlay(&diff_log, hf.start, n)` applies the whole hot
suffix in one call (its ensure IS `data == overlay(base, diff_log, lo, hi)`,
replacing mainline's per-entry `restore_entry` loop).

Theorem: **`lemma_reconstruct_hot_all`** — `overlay(base, diff_log, hf.start, n)`
reconstructs `snapshots[target]` over every cell, both disciplines. Trail via
`lemma_reconstruct_trail` (identity embedding: `diff_log ==` ghost hot suffix, so
the physical overlay maps onto the ghost overlay through `lemma_overlay_congruent`
+ `lemma_cell_eq_overlay`); unique via `lemma_phys_cell_eq_overlay` (first-write
stratum is `dedupe_first`, the unique first-hitter's value is the snapshot value).
Pop-then-restore grow cells need no separate argument — `frame_inv_range`'s
uncaptured arm forces cells past the layer length into the captured arm.

Example: restoring frame 0 with the trail store replays `[(3,3),(5,5),(30,3),
(31,3),(70,7)]` from the right onto `data`; first-entry-wins means cell 3 lands
on the earliest `old=3`. Result: `[0..10]`.

### 3e. Cold → live restore (memcpy of index-run slices)

Function: the cold path (currently inside external_body `restore_cold`). Replays
the whole hot pool back to `snapshots[cold_count]` (`restore_overlay(0,n)`), then
the surviving cold frames **newest-first** via `restore_run(run.base, vals)` —
each a `copy_from_slice` memcpy of the run's value slice into the live column
(clamped to the current length). Then re-materializes the surviving cold top as
a hot frame.

Theorem: **the telescope** — start `data == snapshots[cold_count]`
(`lemma_reconstruct_hot_all(cold_count)`), and each cold frame `f` replayed
newest-first takes `data == snapshots[f+1]` to `data == snapshots[f]`
(`lemma_cold_replay_step` / the fixed-length `lemma_cold_replay_step_l`), bottoming
out at `snapshots[target]`. A covered cell is overwritten by the run
(`cold_value(f,c) == snapshots[f][c]`); an uncovered cell keeps the layer
(`snapshots[f+1][c] == layer_above(f)[c] == snapshots[f][c]`).

Two subtleties that took real work:
- **Fixed-length telescope**: live data is fixed at `saved_len(target)` while
  intermediate `snapshots[f]` vary in length (saved-lens are not monotone under
  pop-into-marked). `lemma_cold_replay_step_l` reconstructs over
  `min(L, snapshots[f].len())`; cells beyond an intermediate snapshot are
  "pending" (restored by an older frame), which is exactly the coverage arm.
- **memcpy composition**: `restore_run` overwrites its window; runs must be
  cell-disjoint (`cold_runs_disjoint`) so a later run does not clobber an
  earlier one and `cold_value`'s covering run is unique.

Example: cold frame with run `{base:3,len:3,start:0}` and pool `[a,b,c]` restores
`data[3..6] = [a,b,c]` by one `copy_from_slice`.

### 3f. Re-materialization (cold top → hot), and the ghost dedupe update

Restoring to a cold target leaves the surviving top frame cold, but `Vec::wf`
requires the open frame to be hot. `restore_cold` decodes the top cold frame's
runs back into `diff_log` (each covered cell `c` → entry `(cold_value(f,c), c)`
via `try_from_usize`, whose `as_nat` is `c`) and pushes it as a hot frame.

Theorem: **`lemma_remat_frame_inv`** — the decoded `diff_log` stratum satisfies
`frame_inv_range` (a covered cell's lowest hitter carries `cold_value == snap`;
an uncovered cell keeps the layer).

Design decision (**ghost re-mat dedupe update**): the decoded `diff_log` is the
*deduped* run decode, but the trail store's ghost stratum for that frame is the
*raw* temporal trail. For the trail discipline `wf`'s sequence-bridge requires
`diff_log ==` the ghost hot suffix, so at re-mat the frame's **ghost stratum is
replaced by the deduped decode** (reconstruction-equivalent by
`lemma_overlay_dedupe_first`), making both sides deduped. The re-mat frame's
ghost `frame_inv` is then a `lemma_frame_inv_range_shift` of its physical one.

## 4. `Vec::wf` and the wf re-establishment after restore

`wf` is phrased against the ghost (D5): `wf_for_snap` (store wf, stack tiling,
`frame_inv_range` over `full_trail`), `repr_ok` (cold pool partition),
`cold_runs_disjoint`, the capture-flag bridges (physical over `diff_log`, ghost
over `full_trail`), `index_set_ok` and the per-frame `frame_iso` (physical↔ghost
index-set equality), the trail sequence-bridge + alignment (`!unique`), and the
unique physical `frame_inv`.

Two invariants were true-but-unstated and had to be added (both maintained by all
mutators): **`frame_iso`** (per-frame index-set equality — the top-only
`index_set_ok` is lost when a frame is buried, and restore promotes a buried
frame) and **`frame.saved_len == snapshots[k].len()`** (the resize target).

Restore re-establishes `wf` by transferring survivor clauses across the
truncation and composing:
- survivors keep `frame_inv` (`lemma_restore_survivors_frame_inv`, and the
  cold/prefix variant `lemma_restore_cold_survivors_frame_inv`), physical
  `frame_inv` (`lemma_restore_survivors_phys`), `frame_iso`
  (`lemma_restore_survivors_frame_iso`);
- structural + trail bridges (`lemma_restore_hot_structural`), trail
  `index_set_ok` (`lemma_restore_index_set_ok_trail`);
- the whole hot-target wf is composed by `lemma_restore_hot_wf` (+ its
  `_snap` half, split for the rlimit).

## 5. Mainline reference (how the single-stack round trip was proved)

The tiered proof reuses mainline's template. For the mark/restore round trip with
the parallel and inline stores (single stack, no tiering), read:

- **`doc/design/05-flat-central-lemma.md`** — the flat reconstruction lemma
  (`lemma_snap_eq_overlay`): overlaying a frame's diffs onto the layer above
  reconstructs its snapshot. This is the core; the tiered `lemma_cell_eq_overlay`
  is its per-cell form.
- **`doc/design/04-pop.md`** — pop into the marked region (why saved_len is not
  monotone), which is the source of the grow-region / fixed-length subtleties.
- **`doc/design/08-token-reuse-and-restore.md`** — restore's structural
  precondition and token validity (the genealogy layer, kept separate here:
  `restore_frame` is genealogy-free, the wrapper `restore` adds the cut).
- **`doc/design/09-diff-stack-compression.md`** and
  **`doc/design/11-parallel-and-eager-compression.md`** — the compression design
  and the parallel/eager variants.

The mainline **proof** to mirror is `Vec::restore` on `git show
main:containers-verus/src/vec.rs` (the `restore` fn, no external_body): resize →
`begin_restore` (named-slots discharge from the no-stray + capture bridge) →
flat-lemma reconstruction → per-entry replay loop → truncate → `finish_restore`
→ inline `wf` re-establishment. `restore_hot` is a direct adaptation of it, with
`restore_overlay` (one batched memcpy) replacing the replay loop and the extracted
parts 1-4 lemmas replacing the inline tail.

## 6. Status and remaining work

Proven (containers-verus verifies at 0 errors): the ghost model + three
equivalences, `restore_frame` (proven tier dispatch), `restore_hot` (entire hot
branch), and all reconstruction/wf lemmas above.

Remaining: `restore_cold` is the sole external_body on the restore path. All its
lemmas exist (`lemma_cold_replay_step_l`, `lemma_remat_frame_inv`, cold survivors,
`cold_runs_disjoint`). What remains is the body assembly:
1. `restore_cold_reconstruct` helper — the two-level loop (outer cold frames via
   the telescope, inner runs via `restore_run`) establishing `view() ==
   snapshots[target]`, isolatable and verifiable on its own.
2. the re-mat + ghost-dedupe update in the body.
3. `lemma_restore_cold_wf` — the cold wf composition (survivors + re-mat frame +
   the ghost-dedupe bridges), split for the rlimit like the hot one.
4. flip `restore_cold` off external_body, then run the full gate battery.

Ledgered external_body (not on the proven restore path, each with a differential
belt): `compress_all_hot`, `normalize_frame`, the cold helpers.

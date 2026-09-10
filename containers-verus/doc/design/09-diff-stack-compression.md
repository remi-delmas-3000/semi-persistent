# Diff-stack compression

Compresses the finalized frames of a semi-persistent vector so the rollback
history occupies close to its information-theoretic minimum. This is a **space**
optimization: it trades finalization time (a per-frame compression pass) for a
smaller history. It is a design doc; CI gates are the source of truth for what
is implemented.

## Purpose and non-goals

**Goal.** Reduce the memory held by the diff history of `VecI`/`VecP` so that
backtracking search over the e-graph stays memory-bounded on long, deep sessions.

**The baseline is the deep copy, not our own uncompressed trail.** Most e-graphs
back up by copying the whole structure, so a search holding `d` checkpoints on
its current path holds up to `d · N` for an e-graph of size `N` — memory scales
*multiplicatively* with search depth. This is why rewrite-intensive equality
saturation and ruleset-search-by-backtracking either deep-copy and exhaust
memory or re-run from scratch and exhaust time. Semi-persistence already replaces
`d · N` with `N + Σ diffs` (*additive*: a checkpoint costs only the delta written
since the previous one). Compression shrinks the `Σ diffs` term, which is the
term that grows with search depth — so it keeps deep searches bounded rather than
saving a constant factor.

Application-class split: for SMT the backtracking is bounded and the workload is
speed-dominated, so compression is not the lever (relevancy/`matchable` is); for
equality saturation and ruleset search the memory scaling above *is* the binding
constraint, so compression is first-order there. The two workload classes want
opposite priorities from the same engine.

Read the doc's "second-order win" language against the right baseline: structure
compression is second-order relative to *our own uncompressed trail on short SMT
sessions*, and first-order relative to the *deep-copy world* on eq-sat sessions.

**Non-goal — wall-clock.** Compression *costs* time at `mark` (finalization) and
adds decode work at `restore`. It does not close a wall-clock gap; if anything
it widens it slightly on backtrack-heavy workloads. Enable it only when memory
is the binding constraint. See `10-shared-fork-history.md` for the wall-clock
lever.

## Current representation

`Vec<T, I, S, TRACK>` keeps a single `diff_log: Vec<(T, I)>` partitioned into
per-frame strata by `frames[k].diff_start`. On `set`, the first write to a cell
below the frame's `saved_len` pushes `(old_value, index)` (first-write-wins, via
the capture bit). `restore` reverse-replays a stratum and truncates. Every
entry costs `sizeof(T) + sizeof(I)`, regardless of structure — a frame that
captured a contiguous range `[i, i+k)` stores `k` redundant indices.

## Design: a layered stack

Split the history into two tiers:

- **Current frame — uncompressed.** A `Vec<(T, I)>` recording diffs as they
  happen, exactly as today. The active frame must stay uncompressed because
  writes arrive one at a time and first-write-wins needs cheap append + the
  capture check.
- **History `[0, current)` — compressed.** On `mark`, the closing frame is
  *finalized*: its diff set is compressed once and appended to a compressed
  store. Finalized frames are read-only until popped by `restore`.

This matches the invariant that only the top frame is ever mutated.

## Finalization

A frame's diffs are a **set** (first-write-wins ⇒ at most one entry per cell),
so they may be freely reordered. Finalize:

1. **Sort by index.** Radix sort on the integer indices — `O(p)` for `p`
   captures (a few byte-passes, 256 counters; no `N`-sized buckets, no log
   factor).
2. **Coalesce runs.** One linear pass merges adjacent indices (`idx[t+1] ==
   idx[t] + 1`) into maximal runs. Because the set was sorted, this captures
   *all* contiguity, not just write-order contiguity.
3. **Encode** (below) and append to the compressed store.
4. **Clear capture state** for the frame's cells during the same pass (fused
   with step 2), so finalization stays a single `O(p)` sweep plus the sort.

Cost added versus today's finalize: the radix sort (`O(p)`, larger constant).
Everything else fuses with the clear pass already performed.

## Encoding: irreducible values, compressed structure

Separate what cannot shrink from what can.

**Values — irreducible per cell, but not per frame (RETRACTED as stated).** An
earlier version of this doc claimed the value pool is irreducible: "every
captured cell's old value must be stored, `P · sizeof(T)`, no encoding beats
this." That is true only cell-by-cell. It is false across a frame or a column
whenever the *multiset* of old values has low cardinality, because a dictionary
collapses repeats using only `Eq` on `T` — it assumes no structure in `T`'s
bits, so the original out-of-scope argument does not apply. The union-find
`parent` column is the case that breaks the claim: path compression re-points
whole paths at one representative, so one id recurs as the old value across many
captured cells, scattered across the array rather than confined to one
contiguous index run. See "Value axis" below; the pool term drops from
`P · sizeof(T)` to `D · sizeof(T)` for `D` distinct values.

The uncompressible residue is only the *distinct* values `D · sizeof(T)` plus
the encoding that says which cell held which value. When `D ≈ P` (all values
distinct) this reduces to the old pool and the index structure below is the only
lever; when `D ≪ P` the value axis is the larger win.

**Structure — a monotone index sequence.** Per frame the touched indices, once
sorted, are a strictly increasing integer sequence; the maximal runs are
determined by adjacency. Its entropy is `~log2(C(N, P_f))`, lower when runs
exist. Two encoders, selected per frame:

### Encoder 1 — singleton-bitmap pooled (simple, near-minimum)

Pools shared across all compressed frames (one allocation each, cache-friendly,
no per-frame `Vec` headers):

- `values: [T]` — `P · sizeof(T)` (the irreducible pool).
- `run_start: [I]` — one cell index per run; `R · sizeof(I)`.
- `run_is_singleton: bitset` — `R` bits.
- `run_len_long: [varint]` — lengths only for non-singleton runs.
- `frame_run_ofs: [u32; F+1]` — where each frame's runs begin (run count and
  value slice implicit by difference).

Length is genuinely independent information (maximal runs have unknown gaps), so
it must be carried; the singleton bitmap carries it at ~1 bit for the common
length-1 case and a varint otherwise. Worst case (all singletons) is
`P · sizeof(I) + P/8 bytes` — uncompressed plus one bit per entry. A run of
length `L` saves `(L-1) · sizeof(I)` for one bit plus a small varint.

### Encoder 2 — Elias-Fano (maximum ratio)

Encode the sorted index sequence with Elias-Fano: `P · (2 + ceil(log2(N/P)))`
bits, within a constant of the `log2 C(N,P)` entropy bound, with O(1) access.
Runs are exploited implicitly (consecutive indices share high bits and step the
low bits, so a run is nearly free) and there is **no singleton penalty** — the
encoding is uniform, spending bits proportional to the actual gaps. Values stay
in the same irreducible pool; frame boundaries as above. This is the
max-compression target; it is heavier to implement and to verify, so it lands
after Encoder 1.

### Encoder 3 — delta + varint (byte-aligned, sequential)

Store the gaps between consecutive sorted indices as varints: a contiguous or
near-contiguous frame becomes a string of 1-byte gaps. An alternative to
Elias-Fano for the index structure, chosen by the per-frame selector.

The reason it earns a place despite Elias-Fano's better asymptotics: the only
read of a compressed frame is whole-frame **sequential reverse-replay** on
restore — no cell is ever random-accessed. Elias-Fano's `O(1)` select/rank is
therefore spent capability. Delta+varint decodes front-to-back, exactly restore's
pattern, is byte-aligned (no bit extraction on the hot path), and its
encode/decode bijection is materially simpler to verify.

The catch is a floor: varint costs `>= 8` bits per index. Elias-Fano spends
`2 + ⌈log₂(N/P)⌉` bits, which drops below 8 when the frame is dense
(`N/P < 64`), and a plain bitmap beats both as `P → N`. Union-find frames are
expected dense (path compression sweeps a near-contiguous range), so on the
dominant column EF or bitmap can still win on ratio while varint wins on decode
cost and proof simplicity. Which one fires is the density measurement below, not
a fixed choice.

Varint also encodes the value axis where it helps: the sorted dictionary values
(delta+varint) and the `group_ofs`/`frame_run_ofs` offset arrays (monotone), both
minor next to the pool and index terms.

### Never-worse guarantee

A per-frame selector picks the smallest of the index-structure candidates
{plain indices, singleton-bitmap, Elias-Fano, delta-varint} at finalize (a few
selector bits per frame name the winner), bounding the structure by
`min(candidates) + O(F) bits`. So enabling compression can never enlarge the
history beyond today's plus a few bits per frame.

## Value axis: dictionary and value-major encoding

Orthogonal to the index axis above. A frame's captured old values are a multiset
of `D` distinct values over `P` cells; when `D ≪ P` the pool is compressible with
`Eq` alone. Two encoders, selected per frame by the never-worse rule:

### Value encoder A — dictionary + codes (keeps index-major structure)

- `dict: [T]` — the `D` distinct values, `D · sizeof(T)`.
- `codes: [u?]` — one dictionary index per captured cell, `P · ⌈log₂ D⌉` bits,
  in the same order as the index structure so a cell's index and code align.

Composes with the index encoders unchanged (they encode *which* cells; codes
encode *what*). Pool cost `D · sizeof(T) + P · ⌈log₂ D⌉ / 8` bytes versus the old
`P · sizeof(T)`. Wins when `⌈log₂ D⌉ < sizeof(T) · 8` minus the dict overhead —
i.e. whenever values repeat at all.

### Value encoder B — value-major / inverted (subsumes index RLE)

Invert the primary axis: store each distinct value once, then the *set* of cell
indices that held it.

- `dict: [T]` — `D · sizeof(T)`.
- per value `v`: its index set `S_v` (a monotone integer set) encoded with the
  same Elias-Fano/singleton-bitmap machinery as the index axis.
- `group_ofs: [u32; D+1]` — where each value's index set begins.

Contiguous cells sharing a value cost nearly nothing (Elias-Fano over a run),
so this captures index contiguity *and* value repetition in one structure. It is
the right shape for the union-find `parent`/`rank` columns, where both hold: a
compressed path is a near-contiguous index range that all took the same old
root. Value-major also makes restore value-major — one `dict[v]` broadcast over
`S_v` — which is a cheaper write pattern than one value read per cell.

### Selecting the encoder: exact-size costing, not thresholds

The per-frame choice is made by computing the exact encoded size of every
candidate and taking the minimum. Finalize already pays a radix sort over the
frame; the sizing rides on the same sweep and is cheaper than the sort, so the
selector is optimal by construction — because the candidate set includes plain,
the winner can never be larger than today. No tuned thresholds.

The sweep gathers, in one pass over the sorted diff set:

- `P` — captures (frame size).
- `R` — maximal contiguous index runs (from coalescing).
- `D` — distinct old values (a scratch hashset over the `P` entries; one frame,
  so cheap — the one cost beyond the index sort).
- `N` — the current vector length (the index universe).
- `Σ varint(gap)` and `Σ varint(runlen)` — accumulated during the walk (varint
  byte counts are additive, so exact and free here).

Each candidate's size is then closed-form in those counts:

| candidate | size (bytes) |
|---|---|
| plain | `P·(sizeof(I)+sizeof(T))` |
| singleton-bitmap | `R·sizeof(I) + R/8 + Σ varint(runlen) + P·sizeof(T)` |
| Elias-Fano + pool | `P·(2+⌈log₂(N/P)⌉)/8 + P·sizeof(T)` |
| delta-varint + pool | `Σ varint(gap) + P·sizeof(T)` |
| dictionary + codes | `[best index structure] + D·sizeof(T) + P·⌈log₂D⌉/8` |
| value-major | `D·sizeof(T) + Σ_v EF(S_v) + D·offset` |

**The eligible candidate set is a per-column property, decided statically.** The
value axis (dictionary, value-major) can only pay when the column's value domain
is small or highly repetitive. That is a fact about what the column stores, known
at construction, not something to rediscover each frame:

- **Distinct-payload columns** — the irreducible `values` pool, unique-id
  columns, arbitrary structs — are **index-major only**. They never cost the
  value-axis candidates and never pay the `O(P)` distinct-value pass; `D` is not
  computed for them.
- **Value-repetitive columns** opt into the value axis. The union-find `parent`
  column is the motivating case: path compression makes whole near-contiguous
  index ranges share one old representative, so `D ≪ P` structurally. `rank`
  (tiny integer domain) and any small-domain flag/enum column qualify too; today
  the union-find columns are the only ones worth enabling.

So `const COMPRESS` is per-column, and for a value-eligible column it selects a
scheme *family* (index axis plus value axis) rather than a bool. Within the
eligible set the per-frame winner is still the argmin below, so never-worse holds
per column.

Within the eligible set the decision **factorizes**, since the index axis (which
cells) and the value axis (what values) are independent — the exception is
value-major, which fuses them and is costed as its own joint candidate:

1. best index-major = `min(plain, bitmap, EF, varint)` for structure, plus
   `min(plain-pool, dictionary+codes)` for values.
2. value-major, costed on its own.
3. selector = `argmin` of {index-major, value-major}, a few bits per frame.

Equivalently the winner is governed by three ratios read off the counts — `D/P`
(does the value axis pay), `R/P` (do runs pay), `N/P` (dense enough for EF or a
bitmap to beat varint's `>= 8` bits/index floor) — plus per-value contiguity for
value-major versus dictionary+codes. The code does not branch on these; it costs
all candidates and takes the min. The union-find columns are the reason the
value-major and dictionary candidates exist at all (`D ≪ P` there); the sizing
just confirms it per frame.

## Per-column analysis (e-graph)

Which scheme fits which column, predicted from what each column stores and how a
diff captures it. Every entry is a prediction to confirm with the finalize-pass
counts (`D/P`, `R/P`, `N/P`); the selector self-corrects per frame, so a wrong
prediction costs a pruned candidate, not correctness.

A first-write-wins diff stores the **pre-frame (old)** value to invert a write,
not the new one. This is the pivot: a column whose *new* values repeat (a
union-find pointing everything at one root) does not thereby have repeating
*captured* values.

| column | type | what a frame captures | index dist. | value `D/P` | scheme |
|---|---|---|---|---|---|
| `parent` (UF) | node id | old parent of each re-rooted / path-compressed node | scattered | low when a big class is re-rooted (members shared an old root), else high | **dictionary+codes** if `D/P` low, else plain index-major |
| `rank` (UF) | `u8` | old rank of the few roots whose rank bumped | tiny `P` | low domain, but `P` tiny | **plain** (frame too small for any header to pay) |
| repr `dense` = `ClassData` | 16-byte struct | old struct of touched class slots | scattered, small `P` | `D≈P` (distinct `use_list`) | **index-major** (value axis useless at struct granularity) |
| repr `sparse`, `indices` | index | old position / id on swap-remove | scattered, small `P` | `D≈P` | **index-major / plain** |
| class ring `next` + key | node id / `Opt<key>` | pointers touched by ring splice | few per merge | distinct | **index-major / plain** |
| use-list arena (heads, nodes) | list / node id | head/next pointers; appends are growth, not diffed | few per op | distinct | **index-major / plain** |
| min-pool | `Opt<T>` | AC completion rows | empty under plain EUF | n/a | irrelevant (EUF); index-major with completion |
| per-kind node caches | node id | hash-cons slots touched/invalidated | scattered | distinct | **index-major** |

Two conclusions worth stating plainly:

**No e-graph column has the contiguous-per-value structure that makes value-major
strictly win.** `parent` is value-*repetitive* but not value-*contiguous* (its
touched node ids are scattered), and for a scattered partition value-major's
per-group Elias-Fano costs `≈ EF(all) + P·log₂D` — exactly the code bits
dictionary+codes pays — so the two are equivalent there, and dictionary+codes is
the simpler form. Value-major would win only if node ids were allocated
per-class so a re-rooted class occupied a contiguous index range; they are not.
So enable **dictionary+codes** on `parent`, not value-major. (This narrows the
earlier "union-find is the value-major case" claim: it is the value-*dictionary*
case.)

**The value-repetitive fields in `ClassData` are buried by array-of-structs.**
`atomic`, `matchable` (bools) and `min_row` (mostly `None`) repeat heavily, but
they are packed inside the 16-byte struct, whose whole-struct value is distinct
per class, so the struct column sees `D≈P` and gains nothing. Splitting
`ClassData` into per-field columns (struct-of-arrays) would expose bool/`Option`
columns that a bitmap compresses to bits — a separate structural lever
(SoA vs AoS), out of scope here but the only way the class-payload column gets a
value-axis win. Recorded so it is not confused with the `parent` case.

## Restore and clear over compressed frames

- **Restore** to frame `d`: reverse-replay compressed frames `current-1 … d+1`,
  then the uncompressed current frame; truncate. A compressed frame replays run
  by run — `values[run] → cells[start .. start+len]` as a slice `memcpy`
  (vectorizable, cache-linear), versus `len` individual `restore_entry` calls.
  Intra-frame run order is irrelevant (disjoint indices under first-write-wins);
  only reverse *frame* order matters.
- **Clear** (fused into finalize, above): a run clears a contiguous stamp range.
  For `VecP` this is whole `u64` bitmap words over `[start, start+len)` — the
  largest single win, since `VecP` otherwise zeroes the whole materialized
  bitmap. For `VecI` the tag bits are interleaved in the value words, so it is
  still per-cell but sequential (cache-friendly).

## Complexity

| | uncompressed (today) | compressed |
|---|---|---|
| finalize (`mark`) | `O(p)` clear | `O(p)` radix sort + coalesce + clear |
| restore | `O(diff)` per-cell | `O(diff)` slice `memcpy` per run |
| history memory | `P·(T+I) + F·usize` | `P·T` + near-entropy structure |
| VecP mark clear | `O(N/64)` whole bitmap | `O(runs + touched/64)` |

## Runtime selection

A const generic beside `TRACK`:

```
pub struct Vec<T, I, S, const TRACK: bool = true, const COMPRESS: bool = false>
```

`COMPRESS = false` keeps today's single uncompressed `diff_log` (zero cost when
off — the compressed store fields compile out like `TRACK=false` does).
`COMPRESS = true` uses the layered stack and the chosen encoder. The choice is
orthogonal to `VecI`/`VecP` (compression lives in the frame representation, not
in where the capture stamp lives), so both gain it. Type aliases expose the four
combinations.

## Verification

Two structural theorems, orthogonal to the existing mark/restore proofs:

- **Encode/decode bijection.** The compressed frame decodes to exactly the set
  of `(index, old_value)` it was built from — proved for each encoder
  (singleton-bitmap, then Elias-Fano) as a pure data-representation refinement.
- **Restore equivalence.** Restoring from a compressed frame yields the same
  `view()` as restoring from the uncompressed diff — reduces to the bijection
  plus the existing disjoint-index replay argument.

Because these are representation refinements over the *same* abstract model, the
mark/restore logic and its proofs are reused unchanged; `COMPRESS` selects the
frame representation behind the abstraction.

## Alternatives considered

- **Per-run `(start, length)` or `(start, value_offset)`**: wastes a field per
  singleton (`R = P`), strictly worse than uncompressed on scattered frames.
  Rejected in favor of the singleton bitmap / Elias-Fano, which have no
  singleton penalty.
- **No sort, write-order runs only**: `O(p)` with no radix pass, but misses
  contiguity written out of order. Since reordering is sound (the frame is a
  set) and radix keeps it `O(p)`, full sort is preferred for maximum ratio.
- **Compressing the value pool via `T`'s bit-structure**: impossible without
  assuming structure in `T`; out of scope. (This is the only value-compression
  claim that holds. The earlier blanket "the value pool is irreducible" was
  wrong: dictionary and value-major encoding compress the pool using `Eq` alone,
  needing no bit-structure — see "Value axis". Kept here as a retracted claim so
  it is not re-proposed.)

## Benchmark plan

Report peak memory and wall-clock for `COMPRESS ∈ {false, true}` × `{VecI,
VecP}` × {singleton-bitmap, Elias-Fano} on the Sundance regression corpus and
saturation runs. Expect: memory down (proportional to run density and
`1/sizeof(T)`), wall-clock flat-to-slightly-up (the finalize sort). Gate a
configuration only if memory is the target; otherwise keep `COMPRESS = false`.
Measure the run-length distribution of real finalized frames first — if frames
are mostly singletons, index-structure compression is not worth the finalize
cost. Measure the value multiset at the same time: per finalized frame and per
column, the distinct-value count `D` against the capture count `P`, and the
index-contiguity within each value group. `D/P` decides whether the value axis
pays and, with the contiguity, whether value-major (encoder B) beats
dictionary+codes (encoder A). Expect the union-find `parent`/`rank` columns to
show `D ≪ P`; expect arbitrary payload columns to show `D ≈ P` and gain nothing
on the value axis. Because the axes are independent, report the pool term and the
structure term separately so each encoder's contribution is attributable.

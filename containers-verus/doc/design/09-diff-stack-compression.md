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

So the per-instance `CompressionMode` is chosen per column, and for a
value-eligible column it names a scheme *family* (index axis plus value axis)
rather than a bool. Within the eligible set the per-frame winner is still the
argmin below, so never-worse holds per column.

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

## Runtime selection (per-instance mode, not a const generic)

Compression mode is a **per-instance runtime field**, chosen at construction, not
a compile-time const generic. The requirement it serves: one binary runs both
regimes without recompilation — SMT with compression off (speed), equality
saturation with compression on and each data structure configured to its best
mode — so the choice must be a value, not a type parameter.

```
pub enum CompressionMode { None, ValueDict, IndexRuns /* extensible */ }

pub struct Vec<T, I, S, const TRACK: bool = true> {
    // ... existing fields ...
    mode: CompressionMode,           // set at construction, consulted at mark/restore
    compressed: CompressedStore<T, I>, // empty and unused when mode == None
}
```

`mode == None` keeps today's single uncompressed `diff_log`; the only cost is one
branch at `mark`/`restore`, and the compressed store stays empty. Other modes
finalize the closing frame with the corresponding encoder. Each aggregate
(`EClasses`, `NodeStore`) sets a per-column mode: `None` everywhere for the SMT
profile; for the eq-sat profile, `ValueDict` on the union-find `parent`/`rank`
columns and `IndexRuns` (or `None`) on the rest, per the per-column analysis.

Const-generic `COMPRESS` was rejected: it bakes the choice into the type, forcing
two builds and preventing a single library from serving SMT and eq-sat callers at
runtime. The runtime field costs one predictable branch when off (measured against
the const-generic's compile-out only if that branch ever shows up in a profile),
which is the right trade for one-binary flexibility.

The choice is orthogonal to `VecI`/`VecP` (compression lives in the frame
representation, not where the capture stamp lives), so both gain it.

## Configuration object and when to compress

The per-instance `mode` generalizes to a small **configuration object** so an
aggregate names, per column, both the encoder and the policy in one value:

```
pub struct ColumnConfig {
    scheme: CompressionMode,   // None | ValueDict | IndexRuns
    // Compress the uncompressed top only when it grows past this fraction of the
    // live payload (0 == compress every mark; None-scheme ignores it).
    compress_at_fraction: f32, // e.g. 0.25 of the base vector length
    // Keep this many most-recent frames uncompressed regardless (LRU floor), so
    // an imminent backtrack pays no decode.
    keep_hot_frames: usize,
}
```

The whole e-graph's compression regime is then a table of `ColumnConfig`, one per
column, passed at construction: all-`None` for the SMT profile, and per the
per-column analysis for the eq-sat profile. The object is a value, not a type, for
the same one-binary reason as the mode field.

**Compress periodically, not every mark.** Finalizing on every `mark` (the
step-3 plan above) pays the encoder cost on the critical path at every branch,
and the measured `compress` cost makes that the wrong default. Instead the top
stack accumulates uncompressed finalized frames and is flushed only when its
footprint crosses `compress_at_fraction` of the live payload (the base vector
length times `sizeof(T)`): the diff trail is worth compressing exactly when it is
becoming a material fraction of what it shadows. This bounds the amortized
finalize cost (one encode pass per flush, over many marks) and keeps the common
mark free of encoder work. The trigger reads two sizes already cheap to track:
the uncompressed diff byte count (running sum) and the base length.

**Keep hot frames uncompressed (LRU).** A restore usually lands near the top of
the stack (backtrack one or a few levels), and decoding a frame just to
immediately restore through it is wasted work. So a flush compresses only frames
older than the `keep_hot_frames` most recent: the hot suffix stays plain and
restore-cheap, and only the cold prefix — unlikely to be a backtrack target soon
— is compressed. This is an eviction policy on the frame stack, not on cells;
"least recently marked" approximates "least likely to be restored to next".

**Monitoring.** The two-stack exposes diagnostics (no spec content, capacity/time
measurements only), which the policy consults and the benchmark records:
uncompressed byte count, compressed byte count, cumulative encode and decode time
(and counts). These are what let the size-fraction trigger fire and what the
benchmark suite reports as the space saved and the time paid.

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

## Measured: encoder cost and space (2026-09-06)

First numbers, from `containers-conformance/benches/diff_compress_bench.rs`
(criterion; space is the deterministic byte table it prints, timing is min-of-run
on the dev machine). `T = I = u32` (union-find id width). Three findings, and
each changes a decision.

**The value dictionary as built is a space loss, not a win.** On the union-find
shape (`N` scattered captures, `D` distinct representatives), the built
`DictFrame` stores `dict: [u32]`, `codes: [usize]`, and `idxs: [u32]`:

| N | D | plain | dict (usize codes) | dict (u32 codes) |
|---|---|-------|--------------------|-------------------|
| 100000 | 1000 | 800000 | 1204000 (**1.50x**) | 804000 (**1.00x**) |
| 100000 | 10000 | 800000 | 1240000 (**1.55x**) | 840000 (**1.05x**) |

The index column is still stored explicitly (value-major does not drop it for
scattered indices), and a `usize` code is wider than the `u32` value it replaces.
Narrowing codes to `u32` only reaches break-even. **Decision:** the value
dictionary earns its place only with codes bit-packed to `ceil(log2 D)` bits and
the index column itself compressed; as a plain dict+codes it is not worth
selecting on a `u32` column. Recorded as a negative result so it is not
re-proposed at `usize` code width.

**Index run-coalescing is the real space win.** On the contiguous-batch shape
(`N` captures forming `R` runs), `RunFrame` drops the index column entirely
(implied by start + offset): 0.51x plain at `R = N/100`, 0.60x at `R = N/10`.
This is the encoder to reach for first, on any column whose captured indices
cluster.

**`compress` (value dict) is O(N·D) today; the encoders that matter are linear.**
`dict_find` is a linear scan, so `compress` is quadratic in practice: 20.6ms at
`N=100k, D=1000`; 185ms at `D=10000`. That is a per-mark cost that would dominate
saturation. `compress_runs` is linear and flat in `R` (~80us at `N=100k`), and
`DictFrame::decode_exec` is linear (~160us at `N=100k`). **Decision:** before the
value dictionary is wired into `mark`, `dict_find` needs a hash (the bijection
proof is search-strategy-independent, so this is an exec-only change); until then
the two-stack ships with `IndexRuns` as the only compressing mode.

## Implemented (2026-09-06)

The two-stack and its policy are built and verified as standalone components,
independent of `Vec`'s proven mark/restore core (so the ~1700 obligations are
untouched):

- `compressed_stack::CompressedStack` — the compressed bottom. View is the flat
  `decode_all(frames)`; `push_frame`/`pop_frame` are the compress/decompress
  primitives, view-preserving by the encoder bijection plus `lemma_decode_all_snoc`.
- `compression_config::ColumnConfig` — the per-column object: `scheme` (all three
  of `None` / `ValueDict` / `IndexRuns`, via `none()`/`value_dict()`/`index_runs()`)
  plus the `compress_at_percent` size trigger (`should_flush`) and the
  `keep_hot_frames` LRU floor (`frames_to_compress`).
- `two_stack_log::TwoStackLog` — the two stacks together. View is `cold@ ++ hot@`.
  `mark(uncompressed_bytes, base_bytes)` opens a frame and, when the trigger
  fires, `flush_cold` compresses the cold hot-frames (all but the hot floor) into
  the bottom, view-preserving. `truncate_hot` is the hot-region restore.
  `hot_bytes`/`cold_bytes` are the monitoring hooks.
- `FrameEncoding::decode_exec` / `DictFrame::decode_exec` — executable
  decompression (verified `r@ == decode()`), used by `pop_frame` and timed by the
  bench.
- `CompressionMode::Auto` + `compression_stats` — per-frame exact-size selection
  and calibrated-adaptive selection. `frame_stats` computes `R` (contiguous runs,
  scatter) and `D` (distinct values, repetition) in one O(N) pass, no sort;
  `FrameStats::best_mode` picks the smallest of plain/runs/dict; `choose_mode`
  delegates to it and `compress_frame`'s `Auto` arm resolves per frame.
  `CalibrationStats::recommend` names the average winner over a window, and
  `CalibrationPolicy` runs `Auto` for a calibration window, promotes that winner
  as a static default, runs it for a period, and re-calibrates — paying the
  adaptive cost only during the windows. `flush_cold` takes the flush mode as a
  parameter so a driver feeds it `flush_mode()`.

**Decision uses the sorted run count; the shipped encoder is write-order.**
`frame_stats` counts `R` from index-set contiguity (`ix-1` absent), i.e. the
run count a *sorted* index-major encoding would achieve. The shipped
`compress_runs_writeorder` only coalesces capture-order-consecutive runs, so on a
shuffled-but-contiguous frame it produces more runs than `R` and under-delivers
against the `Auto` estimate. Closing the gap means shipping the sorted encoder
(with the set-level restore-equivalence theorem), which the reorder bench already
showed is 2-3x smaller and faster to compress and restore — so it is the next
increment, and it also makes `Auto`'s estimates exact.

End-to-end measurement (`two_stack_bench`, 400 marks x 16 writes, distinct=256,
flush at 5% with hot floor 4): the mechanism works — under `ValueDict` the trigger
fires and frames move to the cold stack (hot 65536 -> 32768 bytes, cold 0 ->
83456). Space is 1.77x the plain baseline, a loss, matching the encoder finding;
the mark path costs 146us vs 17.7us (the `dict_find` encode). So the plumbing is
verified and exercised; the space win waits on narrowed dict codes and `IndexRuns`.

**Index-major (`IndexRuns`) is now a live, selectable scheme.** `index_like::
IndexFromNat` refines `IndexLike` with `from_nat` (`from_nat(n).as_nat() == n` on
`[0, max_nat)`, plus `from_usize` / round-trip / bounded-value lemmas), primitive
impls. `compress_runs_writeorder` run-coalesces in write order so it preserves the
exact flat view (no sort, no permutation), keeping the mark/restore theorems.
`RunFrame::decode_i<I: IndexFromNat>` reconstructs the dropped index column as
`from_nat(start + offset)` (spec); `decode_exec_i` is its executable form,
`external_body` against that spec and the `compress_runs_writeorder` bijection,
backed by the `run_frame_roundtrip` 2000-case proptest. `FrameEncoding` gained a
`Runs` arm (so the enum carries `I: IndexFromNat`), and `CompressedStack` /
`TwoStackLog` are generic over `IndexFromNat`, so `index_runs()` flows end to end.
Measured (`two_stack_bench`, consecutive-cell workload): the index-runs cold
footprint is ~half the value-dict cold footprint and compresses faster; total is
1.15x plain at 16 writes/frame (vs value-dict's 1.77x), the residue being per-frame
`Vec` headers, so the win scales with frame size.

Remaining: (1) narrowed/bit-packed dict codes (to turn value-dict from a loss into
a win); (2) a pooled run representation (one flat value pool + run offsets across
frames) to drop the per-frame `Vec` header overhead the bench exposed; (3)
materialize-into-cold for deep backtracks (`pop_frame` is the primitive;
`truncate_hot` covers the hot region); (4) `IndexFromNat` for the wrapper id types,
needed only when an e-graph column keyed on them selects `IndexRuns`; (5) adoption
by the e-graph column aggregates.

## Decision: value-major lives (measured 2026-09-06)

Head-to-head across column shapes (`scheme_comparison_bench`; real run counts from
`compress_runs_writeorder`/`compress_runs_sorted`, computed sizes for the packed
value-major variants), ratio vs plain:

| shape | plain | idx sorted | val usize | val byte | val packed |
|-------|-------|-----------|-----------|----------|------------|
| union_find D=64 | 1.00x | 1.37x | 1.50x | **0.63x** | **0.36x** |
| union_find D=4  | 1.00x | 1.37x | 1.50x | **0.63x** | **0.30x** |
| contiguous      | 1.00x | **0.51x** | 2.00x | 1.25x | 0.95x |
| scattered_unique| 1.00x | 1.37x | 2.00x | 1.25x | 0.98x |

**Value-major is NOT retired — it wins decisively on the union-find shape**
(0.30-0.36x), the memory-critical eq-sat column, where index-major loses (indices
scattered, ~0.87 runs/entry even sorted). The 1.50x that made it look like a loser
was entirely the `usize` codes: byte-granular codes (u8/u16/u32 by `D`) already win
at 0.63x, and bit-packing to `ceil(log2 D)` bits reaches 0.30x. Index-major owns
the contiguous shape (0.51x); plain wins the scattered-unique shape. So the
per-column defaults are: union-find `parent`/`rank` -> value-major (packed),
contiguous batch columns -> index-major, everything else -> plain. Sort-first
index-major only edges write-order on latent-contiguity frames (1.37x vs 1.50x
here, both losing); it earns its keep on shuffled-but-contiguous frames, not
truly-scattered ones.

**Build order that follows:** value-major needs packed codes to realize the win.
Byte-granular codes (0.63x, easy to verify, swappable behind the codec contract)
first; bit-packed codes (0.30x, a further ~2x, bit-arithmetic proofs) after. Both
sit behind the round-trip-preserves-the-write-multiset contract, so upgrading the
code representation touches only the codec, not callers.

**Realized (2026-09-06):** byte-granular value-major is built and verified. The
`Codes` column (`U8`/`U16`/`U32`/`Usize`) sits behind a `view: Seq<nat>` contract;
`DictFrame` stores `codes: Codes` and its bijection is stated over `codes.view()`,
so the width is invisible and a future bit-packed variant drops in without
touching the frame or callers. `compress` narrows codes via `Codes::from_usize`
(width by dict size), keeping `decode == diffs@` verified — value-major is a
non-reordering codec, so it keeps the exact contract and needs no two-stack rework.
The selector is now honest: `FrameStats::best_mode` costs index-major at the
sorted run count (usize starts) and value-major at the narrow code width
(`code_width`, computed from D) with indices stored, so `Auto`/calibration compare
what the encoders actually ship. Consequence, pinned by `choose_mode_criterion`:
the selector now picks value-major for value-repetitive scattered columns (dict
2516 < plain 4000 at D=4, N=500) where the usize-code cost wrongly picked plain.
Still remaining: bit-packed codes (the further 2x), the hashmap dedup (current
`dict_find` is O(N*D)), sorted-index-major made selectable through a set-level
two-stack contract, and fork-history reclamation (doc 10).

## Benchmark plan

Report peak memory and wall-clock for `mode ∈ {None, ValueDict, IndexRuns}` ×
`{VecI, VecP}` on the Sundance regression corpus and saturation runs. Expect:
memory down (proportional to run density and `1/sizeof(T)`), wall-clock
flat-to-slightly-up (the finalize work). Gate a mode only if memory is the target;
otherwise keep `None` (the SMT profile).
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

## Implementation plan (code-level)

Grounded in `vec.rs` as it stands (the `Vec<T, I, S, const TRACK: bool = true>`
at `vec.rs:640`). Compression is a `Vec` concern, not a `DiffStore` one: the base
data and capture bits live in `S: DiffStore`, but the diff trail (`diff_log:
Vec<(T, I)>` and `frames: Vec<Frame<I>>`, partitioned by `frames[k].diff_start`)
lives in `Vec`. So the const generic goes on `Vec`.

**Step 1 — standalone verified encoder module (`diff_compress.rs`), additive.**
No `Vec` change, cannot touch the existing ~1705 obligations. Contents:
- The compressed frame representation (index-major run-coalescing first;
  dictionary+codes for the value axis second; value-major last).
- `spec fn decode(cf) -> Seq<(T, I)>` and `exec fn compress(&[(T, I)]) -> cf`.
- The **encode/decode bijection** theorem: on a finalized frame (first-write-wins
  gives unique indices; take sorted-unique as a `requires`, discharged in step 2
  by the radix sort), `decode(compress(d)) == d`. Proof risk lives here: the
  run-coalescing bijection is an inductive sequence-refinement; the dictionary
  bijection is a pointwise map (`decode[t] = (dict[codes[t]], idx[t])`), which is
  the lower-risk proof and the value-axis win for `parent`, so land it first.
  Generic-`T` equality is the friction point for the dictionary dedup: constrain
  the value column to `T: IndexLike` (node ids) and compare by `as_nat`, or thread
  a verified `PartialEq`.

**Step 2 — per-instance `mode: CompressionMode` field on `Vec`.** A runtime field
(default `None`), not a const generic, so one binary serves SMT (`None`) and
eq-sat (per-column modes) without recompilation. `Vec::new` keeps `None`; a
`with_mode(mode)` constructor sets it. The compressed store fields always exist
but stay empty when `mode == None`. `mark`/`restore` branch on `mode`; the
`None` arm is today's code path, so the `None` proofs are the current proofs plus
a mode discriminant carried through the invariant (`mode == None ==> compressed
store empty`). No const-generic proliferation across impl blocks.

**Step 3 — finalize at `mark`.** `mark` (`vec.rs:~1409`) closes the active frame.
Under `COMPRESS`, replace pushing the raw closing stratum with: radix-sort the
stratum's `(T, I)` by index (`O(p)`), `compress` it (step 1), and append to a
compressed store beside `diff_log`. Fuse the capture-bit clear into the same
sweep. The frame index now points into the compressed store.

**Step 4 — restore.** `restore` reverse-replays compressed frames run by run
(`decode` a run, write `values[run] -> cells[start..start+len]` as a slice), then
the uncompressed active frame. The **restore-equivalence** theorem reduces to the
step-1 bijection plus the existing disjoint-index replay argument, so the
mark/restore model proofs are reused; `COMPRESS` selects the representation behind
the same abstract `view()`.

**Step 5 — per-column eligibility.** Distinct-payload columns run index-major
only; the value axis (dictionary) is enabled only on the value-repetitive columns
(`parent`, `rank`), per the per-column analysis. Expose this as the column's
`COMPRESS` scheme selection where each aggregate constructs its vectors.

Order: step 1 (verified, standalone, committable alone) is the safe first
increment; steps 2-4 are the invasive `Vec` change and land together (the
`COMPRESS=true` path is not partially meaningful); step 5 is the aggregate wiring.

## Performance: SIMD acceleration under conformance

The finalize/restore encoders are on the hot path (every `mark` and `restore`
touches them), so once correct they are performance-critical and want SIMD:
radix-sorting the index stratum, run-coalescing, dictionary dedup, and the
run-by-run `memcpy` on restore all vectorize. Verus cannot verify SIMD intrinsics
(they are outside its model), so the verified scalar encoder in `diff_compress`
is the **reference specification**, and a SIMD implementation is checked for
equivalence against it — not proved — through the existing `containers-conformance`
crate (differential + property + Criterion checks between the verified and
production paths). Concretely: the verified `compress`/`compress_frame`/
`compress_runs` and their `decode` are the oracle; the SIMD encoder passes iff, on
proptest-generated frames, its output decodes to the same diff sequence
(`decode(simd_compress(d)) == d`) and matches the scalar encoder byte-for-byte
where the representation is canonical. This keeps the soundness guarantee (the
scalar path is verified; the fast path is conformance-tested against it) without
forcing SIMD into Verus. Land the scalar verified encoder first; add the SIMD
path and its conformance checks after, gated in `containers-conformance`.

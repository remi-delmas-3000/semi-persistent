# 20. Hot-Path Discipline: Writing Verified Code the Optimizer Can Optimize

[← 19 Verified Node Caches](19-verified-node-caches.md) · [Table of contents](00-table-of-contents.md)

## Purpose

The verified containers must not be slower than the legacy ones they replace,
and the proofs must not be the reason when they are. Proof text is erased
before code generation, so it cannot cost cycles directly; what costs cycles is
the *shape* the executable code takes to make the proofs tractable, and what
that shape does to LLVM's heuristics. This chapter records each optimization
hint raised during the 2026-09 performance work, states whether the code
confirms it, gives the measurement or the disassembly that decides it, and
turns the confirmed ones into rules. The audit tool and the probes that
produced the evidence are in `tools/codegen_audit.py` and
`containers-conformance/examples/codegen_probe*.rs`; the findings are in
`doc/tasks/codegen-audit-2026-09-22.md`.

Speedups below are reference time divided by new time, so above 1 is faster.

Status reconciled against committed `ae79d6a` (2026-09-24). Measurements below
are historical results of the named experiments, not a fresh gate or CI run.
The slice-length change recovered the append peel, but the committed fixed-count
append result remains about 0.92× the pre-merge verified reference. The remaining
gap is open. Uncommitted append experiments are not part of this design.

## Governing principle

> Write the source so that the optimizations we rely on trigger reliably,
> not by heuristic luck.

Confirmed, and it is the single most important finding of the audit. The
list-arena append benchmark ran 0.79× against the pre-merge mainline with
byte-identical executable statements in the list layer. Forcing LLVM to peel
one loop iteration restored it exactly (103 µs against mainline's 103 µs;
unpeeled 128 µs), and the legacy container gained the same 25 per cent under
forced peeling. Mainline's advantage over legacy was a peel the heuristic
happened to choose, and a change below the list layer withdrew it. A
performance property that depends on a heuristic firing is not a property;
the source has to hand the optimizer the invariant it needs, in a form it
recognises, every time.

## The hints, one by one

### H1. "Can we try to inline everything?"

**Partly confirmed.** Inlining matters exactly where a call sits on a
per-element path; blanket inlining does not.

- Confirmed: `VecD::try_push`, `try_extend`, `pop`, `push_untracked`,
  `set_untracked` and the same entry points on `Vec` carried no inline
  attribute and were called out of line per element (only the get and set
  family was marked); the static parallel-store `try_push` likewise. With
  `#[inline(always)]` the untracked push and pop row measures 1.14× (128.8 µs
  to 112.7 µs, round B of the paired run). Earlier in the same programme,
  `intern_entry` marked inline-always closed a 4 to 5 per cent interning
  deficit.
- Refuted as a general remedy: forcing the whole list-arena constructor chain
  inline changed the append loop by one instruction and did not restore the
  peel; marking `try_append` and `append_raw` inline-always removed the call
  and left the timing at 0.79×.

**Rule.** Every function on a per-element path that is not already inlined by
the heuristic is marked `#[inline(always)]`; the audit tool's "out-of-line
calls into the verified crate" column is the checklist. Nothing else gets the
attribute on speculation.

### H2. "Can we enable LTO?"

**Already in place.** The release profile has `lto = "fat"` and
`codegen-units = 1`. There is nothing to add; cross-crate inlining is not the
limiting factor anywhere the audit looked.

### H3. Code alignment flags

**Refuted by measurement.** `-align-all-blocks=6` moved branchy rows to 0.31×
to 0.60×; `-align-all-functions=6` was neutral. Unchanged code also showed
±8 per cent drift between binaries (the `aov/log` row); alignment is a possible
contributor, not an established sole cause. That drift is why the paired protocol runs two interleaved rounds and treats
the legacy arm as a canary; it is not a lever.

### H4. "Hoist all constant values out of loops"

**Confirmed, with a precise scope.** The library does not own the loop; the
caller does. What the library can do is read each field once per operation
and pass the proven facts down, so that inside the caller's loop there is
nothing left for the compiler to re-prove invariant. The audit found the
opposite pattern on every hot path:

| path | reads of one unchanging value per operation |
|---|---|
| list append | node count 4× (`raw_len`, `nodes_len` twice, `store.len`), heads length 2× |
| vector iterator `next` | length 3× |
| ring `add_singleton` | length 3× |
| union-find `union_core` | length 2×, then `find` checks again |
| e-classes `merge_with`, `prefer_a_by_uses` | length 2×, roots found twice |
| tracked `set_index`, no frame open | two frame-stack lengths, the watermark and the data pointer, every element |

These are historical source-level observations, not a claim that every read
survives compilation. Whether LLVM folds a read depends on alias information
and surrounding code; inspect the concrete generated loop. SparseSet lookup
reuse, for example, measured neutral because repeated loads were already folded.

**Rule.** *Check once at the public boundary; internal cores carry the fact
as a `requires` and never re-check.* `Vec::get_index`/`set_index` stay total
(explicit bound, refuse on failure) and delegate to `get_at`/`set_at`, whose
bound is a precondition; `ListArena::append`/`prepend` call the raw cores
directly because every caller already proves the id-range facts the old
runtime re-check tested. The same split applies to the union-find, e-classes
and sparse-set paths in the table above.

### H5. "Invert the branching logic to branch on const generics before anything else"

**Confirmed, with one nuance.** LLVM folds `TRACK && x` wherever `TRACK`
appears in the conjunction, so the *branch* order is not the issue; the
*reads evaluated before the test* are. `hot_defer_scope_exec` computed three
`let` bindings (the store flag and two frame-stack lengths) before the
`TRACK && ...` conjunction; the lengths come from std's `Vec::len`, which
attaches an `llvm.assume` to the loaded value, and the inspected compilation retained loads feeding those assumptions.
This is not a general rule that every assume or its input load survives
optimization. The result was six loads of the frame
stacks per iteration inside the *untracked* list append loop. The
short-circuit form removes them. Elsewhere the const generics are already
first in every conjunction; the runtime store enum (`VecD`) dispatches on a
runtime value by design and is out of scope; `UnionFind::try_make_set` tests
the two proof columns without an outer `if PROOFS` (to confirm whether the
option tests fold).

**Rule.** A const-generic test is the first thing evaluated in any function
whose behaviour depends on it, and no read is performed before it. Not
because the branch would survive, but because the reads would.

### H6. "Never re-evaluate values that cannot change"

**Confirmed.** This is H4 stated from the other side; the table and the rule
are the same. One addition from the review: the tracked write path formerly kept
*two* executable implementations (the Hot projection and the general path)
behind a per-element choice, and under the Hot condition they did the same
work. Commit `350e1e1` replaced that split with one executable path per operation. The rule for that case is one executable implementation with separate
proof cases; no cached "which tier" flag, because the flag's correctness
across explicit migrations would be a new obligation and the flag becomes
pointless once the split is gone. Note that the write skeleton fits `set`
only: `push` must still inherit the captured flag when re-entering a popped
saved slot, and `pop` must capture the last element before removing it.

### H7. Loop peeling and unrolling

**Partially resolved.** The slice-length change restored peeling and recovered
most of the measured append regression. It did not close the entire gap.

The mechanism, read from the per-pass IR of the benchmark closure on the
pre-merge mainline (85e9de3) and on the first commit that lost the peel
(7ece790, found by bisection with the append benchmark's verified-to-legacy
ratio as the oracle):

1. In the inspected compilation, peeling becomes possible when a loop-header phi
   becomes invariant after the first iteration. On mainline the append loop's
   header carries `phi i1 [l < heads.len, entry], [true, latch]`: the heads
   bound check as a boolean, `true` on the back edge because the same check
   is re-done after the node push and dominates the latch.
2. That boolean phi is InstCombine folding a compare of a phi into a phi of
   compares. The fold requires the phi to have a single use. Our header phi of
   the raw heads length has two: the compare, and an `llvm.assume` that
   std's `Vec::len` attaches to every length it returns (`len <= isize::MAX /
   size_of::<T>()`).
3. The assume folds away only when the phi's range is already known: on
   mainline the loop entered with the heads length as the constant 2000,
   because the benchmark closure was optimized as its own function first and
   its GVN seeded the length from the constructor's visible `len = 0` store.
   7ece790 grew the constructor (`GenStamps::new` with a loop) past the early
   inliner's budget, the seed became an opaque call, the entry value became a
   load of unknown range, the assume survived, the fold did not fire, the
   peel did not fire. Later commits changed the closure's inlining order, so
   restoring the constructor's visibility alone no longer helps (measured:
   no change).
4. The library cannot control what the caller's optimization order makes
   visible. It can control the assume. Reading the length as the slice
   length (`data.as_slice().len()`) returns the same value with no range
   assumption attached, the phi has one use, the fold fires regardless of
   what the entry value is, and the peel follows. Measured on the append
   benchmark: verified 200 µs to 170 µs with the legacy arm flat, ratio 0.99
   to 0.84 (mainline 0.79); the closure's inner loop goes from 52 to 38
   instructions, mainline's shape.

Ruled out along the way, each by one measurement: the constructor's
visibility (inlined the whole chain, no change), moving the head write before
the node push (worse, 1.10×), raising GVN's memory-dependence scan limits (no
change), a config-read barrier (no atomic load in the loop). Forced peeling
(`-unroll-force-peel-count=1`) takes the legacy arm to the same 160 µs, which
supports peeling as a major contributor. A global peeling flag can affect
other loops; it does not attribute the entire remaining gap to this loop.

One reach limit, measured after the fix with an opaque-input variant of the
same benchmark: the inspected fixed-count loop peeled, whereas its runtime-count twin did
not. This is an observation about these builds, not a general restriction on
LLVM peeling. With a runtime count neither arm was peeled and the
verified append is at parity with legacy. The rule below still holds, since
the assume is the library's to remove and costs nothing; the peel it enables
is the caller's constant to provide.

**Rule.** *A length read on a per-element path returns the slice length, not
`Vec::len`.* std's `Vec::len` is not a plain load: it carries an assumption
that keeps the loaded value alive as a separate use and can block the
phi-of-compare fold that loop peeling depends on. The store accessors
`raw_len`, `len` and `is_empty` follow the rule; `wf` proves the same bound
for verification, so the value-level contract is unchanged. LLVM does not
receive that erased proof; removing an assumption can also remove useful
optimizer information in other contexts. More generally: an executable
statement that only *tells the compiler something* is still an executable
statement with consequences, and the proofs already carry the fact.

### H8. Pooled storage for hint lists

**Open, unchanged.** The `HintSlot` is width-generic (a `Tagged` repr of the
id family); the pooled linked-node arena for hint lists was designed
(chapter 19) and not built. No measurement bears on it yet.

## Second-pass review findings

Historical work queue. The order-of-work section below records completed
waves. Specifically: `diff_log` removal, adaptive byte accounting, SparseSet
lookup reuse, UnionFind root reuse, EClasses batch initialization, B+ cursor
changes, SpMap cloning, HintedArena probing, LayeredSpanMap flatten, and
TwoStackLog zero-flush work have landed. List append/prepend construction and
typed-ID changes have also landed. Dict sequential decoding is complete;
that does not establish completion of every layered/delta decoder or builder
reservation opportunity. The impossible-loop question remains open. The
findings column describes the source when reviewed, not necessarily HEAD.

| container | finding | direction |
|---|---|---|
| Vec | `diff_log` is a real `std::vec::Vec` kept as a "proof-compatibility shadow" | make it ghost or remove it |
| Vec | five `loop {}` arms stand in for proved-impossible cases (list arena) | `unreached()` panics; it is not unchecked-unreachable. Preserve semantics and measure alternatives |
| ListArena | `ListNode::default()` then overwrite in append and prepend | construct from the payload |
| Vec | adaptive policy evaluation walks the whole history up to three times per call | compute occupancy from pool boundaries or keep exact totals |
| SparseSet | `try_get` calls `contains` then `get`, which calls `contains` again; `get`/`set`/`remove` reload the sparse position after validation | one internal lookup returning the validated dense position |
| UnionFind | `explain` can run five `find_const` traversals | cache roots, validated internal extraction |
| EClasses | `set_min_monomial` initialises a known-width row by repeated `try_push` | validate headroom once, batch-initialise |
| B+ tree | cursor `seek` always descends from the root; the legacy current-leaf fast path is documented as omitted; `seek` reloads the leaf `seek_leaf` loaded | restore the fast path; return the loaded leaf |
| CircularList | public `splice` walks the absorbed ring to prove disjointness | keep the public guard; proven callers use the core (the e-graph does) |
| SpMap | `intern_entry` clones the key on a hit | defer clone and capacity work to the vacant path; measure against the extra hash |
| HintedArena | `probe` re-indexes the spill slot and re-selects the store per bucket entry | bind once, select once |
| LayeredSpanMap | `flatten` binary-searches invalidations per key | cursor walk |
| Layered decode | `decode_exec` random-accesses every element; the delta decoder replays predecessors | sequential decoder |
| TwoStackLog | `flush_cold(0)` still copies the hot log | zero-work exit; retain allocations |
| builders | known-size copies start empty and push | reserve once |

## Validation protocol

Every change is judged twice, in this order, and the second judgement is the
one that counts:

1. **Codegen audit** (`tools/codegen_audit.py` on the probe binaries): the
   loop shape is inspected for the intended effect. Diagnostic only; an
   unchanged instruction count does not reject a candidate.
2. **Paired benchmark** (`tools/bench_compare.py`, τ = 1.08, two interleaved
   rounds, the pre-change tree as the reference): run regardless of what the
   audit shows. The legacy arm is an execution-condition control, not evidence of core identity: if it moves
   by more than the tolerance between rounds, that round is discarded.

Then the per-commit gate (both feature sets verified, the crate and consumer
tests, the partial-API and trust gates). Every fixed-size row has, or gets,
an opaque-input twin (sizes and payloads through `black_box` once at the
group boundary, one plan shared by both arms, one `black_box` on the result):
a gap that appears only in the fixed row is a compile-time-constant effect and
is reported as such. Coverage added on 2026-09-23: sequential B+ seeks tracked
and untracked, expensive map keys, long compression runs with a zero-frame
flush, union-find explain on a deep chain, min-monomial rows. Still to add:
static and runtime stores, `PROOFS` on and off, repeated capture, pop then
re-push, nested restores, migrated histories.

## Order of work

1. Vec: one executable write path (H6), on the checked accessors (H4).
2. SparseSet lookup reuse.
3. List append on the check-once rule (H4), measured for the peel (H7): done, peel restored by the H7 rule.
4. The repeated traversals (union-find, e-classes, B+ cursor): done
   2026-09-23; the B+ cursor reads through borrowed reprs (no node copy),
   shuffled seek 2.1×, sequential seek 8.8× against the start of the wave.
5. The hash-keyed structures (SpMap intern, HintedArena probe, e-class
   min-monomial rows): done 2026-09-23; `HintedArena` is generic over the
   store like `Vec`, intern hits on heap keys 1.8×, probe 1.1× to 1.9×.
   The CircularList and ListArena rows were already closed (c9ff2bb,
   bc15b6c). Two lessons: a second length read in the same operation is a
   second range check and a second dependency wherever it sits (25 per cent
   on the probe hit path); a bench group's placement noise floor is measured
   (same source, shifted text) before any row inside it is read as a signal.
6. Compression and log items (Vec diff-log shadow, adaptive policy walk,
   `flush_cold(0)`, LayeredSpanMap flatten, Dict decoder): done 2026-09-23.
   The shadow is removed outright (two clears, a shrink, 24 bytes per
   `Vec`; neutral as it should be), the adaptive count reads frame
   boundaries (neutral on the adaptive rows), `flush_cold(0)` exits with
   no work (46× on the zero-frame-flush run), flatten walks an
   invalidation cursor (2.3× dense, 1.26× sparse), the dict decoder
   selects the code width once and walks packed words (1.2× on the cold
   pop run, up to 2.1× on the decode rows). One lesson: "retain the
   allocation" is not free when a policy reads capacity; the flush
   trigger's `hot_bytes` is capacity-based, and a hot log that kept its
   capacity flushed one frame per mark (0.70× on the churn rows), so the
   tail copy stays a fresh vector and the helper says why.

---
[← 19 Verified Node Caches](19-verified-node-caches.md) · [Table of contents](00-table-of-contents.md)

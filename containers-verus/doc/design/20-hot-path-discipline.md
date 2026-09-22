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
to 0.60×; `-align-all-functions=6` was neutral. Alignment explains the
±8 per cent drift of unchanged code between binaries (the `aov/log` row), and
that drift is why the paired protocol runs two interleaved rounds and treats
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

The compiler cannot fold these across the stores the operation itself makes
(it must assume the write may alias the field), so each read survives as a
load, and each surviving load is one more thing the late passes have to
reason about when deciding whether to peel or to keep a value in a register.

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
attaches an `llvm.assume` to the loaded value, and a load that feeds an
assume cannot be dead-code-eliminated. The result was six loads of the frame
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
are the same. One addition from the review: the tracked write path keeps
*two* executable implementations (the Hot projection and the general path)
behind a per-element choice, and under the Hot condition they do the same
work. The rule for that case is one executable implementation with separate
proof cases; no cached "which tier" flag, because the flag's correctness
across explicit migrations would be a new obligation and the flag becomes
pointless once the split is gone. Note that the write skeleton fits `set`
only: `push` must still inherit the captured flag when re-entering a popped
saved slot, and `pop` must capture the last element before removing it.

### H7. Loop peeling and unrolling

**Confirmed as the mechanism, not as a tool.** Peeling is decisive for the
list append (above). The library cannot unroll or peel the caller's loop, and
compiler flags are not a fix. What the library can do is make the peel
trigger reliable: LLVM peels one iteration when a loop-header value becomes
constant after the first iteration, and on mainline that value is the heads
bounds check, forwarded across the back-edge into a boolean that is `true` on
every later iteration. Our loop reaches the same pass with the raw length
carried instead and the check recomputed, plus a second exit from the
id-capacity guard rewritten as an induction-variable test. The pass trace on
the benchmark closure places the divergence in the closure's late GVN and
jump-threading passes (both trees are identical through inlining and the
early loop passes). Whether H4's check-once rewrite restores the peel is a
measurement, still to be made; it is the first candidate because it removes
exactly the reads those passes had to reason about.

Ruled out as the trigger, each by one experiment on an isolated worktree: the
write dispatch (reverted, no change), the constructor's visibility (inlined,
no change), the type's size (mainline padded to 320 bytes still peels), the
drop glue (a forgotten arena, no change), address escape (every callee is
`captures(none)`, no address stored), the pinned frame-stack loads
(short-circuited, no change), the inline attributes (identical on both
trees), the loop-size threshold (doubled, no change).

### H8. Pooled storage for hint lists

**Open, unchanged.** The `HintSlot` is width-generic (a `Tagged` repr of the
id family); the pooled linked-node arena for hint lists was designed
(chapter 19) and not built. No measurement bears on it yet.

## Second-pass review findings

Source-level, unmeasured; each is a bounded change with its own proof.

| container | finding | direction |
|---|---|---|
| Vec | `diff_log` is a real `std::vec::Vec` kept as a "proof-compatibility shadow" | make it ghost or remove it |
| Vec | five `loop {}` arms stand in for proved-impossible cases (list arena) | `unreached()` gives an unreachable-terminated exit; measure, since it is a panic path |
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
   loop shape must change in the intended direction. Diagnostic only.
2. **Paired benchmark** (`tools/bench_compare.py`, τ = 1.08, two interleaved
   rounds, the pre-change tree as the reference): run regardless of what the
   audit shows. The legacy arm is the canary for core placement: if it moves
   by more than the tolerance between rounds, that round is discarded.

Then the per-commit gate (both feature sets verified, the crate and consumer
tests, the partial-API and trust gates). Coverage to add beyond the current
microbenchmarks: tracked and untracked, static and runtime stores, `PROOFS`
on and off, repeated capture, pop then re-push, nested restores, migrated
histories, sequential B+ seeks, expensive map keys, long compression runs,
zero-frame flushes.

## Order of work

1. Vec: one executable write path (H6), on the checked accessors (H4).
2. SparseSet lookup reuse.
3. List append on the check-once rule (H4), measured for the peel (H7).
4. The repeated traversals (union-find, e-classes, B+ cursor).
5. Compression and log items, tracked separately.

---
[← 19 Verified Node Caches](19-verified-node-caches.md) · [Table of contents](00-table-of-contents.md)

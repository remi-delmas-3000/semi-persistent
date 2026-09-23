# Codegen audit of the verified containers (2026-09-22)

Scope: every executable method of the core `Vec` container in each store
(Inline, Parallel, Trail, and the `VecD` enum) and tracking mode, then every
composite (`ListArena`, `SparseSet`, `AppendOnlyVec`, `SpMap`/`SpUniqueMap`,
`UnionFind`, `EClasses`, `BPlusTreeSet`, `CircularList`), each beside its
legacy counterpart where one exists. The question is not "is it fast" but
"did the optimizer do what the source allows": inlining, keeping loop
variables in registers, hoisting invariant loads, folding dead paths.

## Method

Two probe binaries, `containers-conformance/examples/codegen_probe.rs` (Vec)
and `codegen_probe_composites.rs` (composites), hold one `#[inline(never)]`
function per (container, store, mode, method), each running the method in a
tight loop. `containers-verus/tools/codegen_audit.py <binary>` disassembles
every probe and reports:

- **instr**: instructions in the probe function (setup included);
- **inner loop**: instructions in the innermost loop, the per-operation cost
  shape; compare against the legacy row of the same method;
- **verus calls**: out-of-line calls into the verified crate from the probe
  (hot-path inlining failures; growth and construction calls are cold and
  listed separately by the tool);
- **panic paths**: refuse/expect call sites reachable from the probe;
- **carried**: stack slots stored and reloaded inside an innermost loop, a
  loop variable the optimizer kept in memory;
- **dup loads**: stack slots loaded more than once per iteration with no store
  between, a reload the optimizer could not prove unnecessary.

Build: `cargo build --release -p containers-conformance --example codegen_probe
--example codegen_probe_composites`. Rows prefixed `vec_` are the `VecD` enum
with a runtime store kind, so each such probe compiles all three kinds and
its numbers are the union; the `svec_` rows are per static store and are the
ones to compare per kind. `lvec_` rows are the legacy container.

## Findings on `Vec`

1. **Reads are at parity.** `get_index`, `get`, `as_slice` iteration: 8 to 9
   instruction loops, same as legacy, in every store and mode.
2. **Untracked writes are at parity.** `set_index` 8 to 10 versus legacy 8
   to 10; `push` 12 versus 11 to 13; untracked `pop` on the verified side is
   folded to a closed form (no loop left), better than legacy's 11.
3. **Tracked writes with no frame open are the outlier.** `set_index`: 56
   (inline) and 85 (parallel) instructions per element against legacy's 8 and
   21; tracked `pop` on the parallel store 94 against 20. The loop re-reads,
   every element, the two frame-stack lengths, the saved-length watermark and
   the store's data pointer, re-checks bounds twice (the public guard, then
   Rust's index check inside the store), and carries the capture path twice
   (duplicated around the unwind edges). None of it is extra work in the
   source: the watermark is zero with no frame open and every branch skips.
4. **A no-drop twin halves it.** Wrapping the container in `ManuallyDrop`
   (no drop glue, so no landing pads in the loop) takes the tracked
   `set_index` loop from 56 to 26 (inline) and 85 to 32 (parallel) with the
   untracked loop unchanged at 10. The unwind structure that drops the
   container is one confirmed cause; the remaining 26 versus 8 is the
   invariant reloads.
5. **Hot forwarders were not inlined.** `VecD::try_push`, `try_extend`,
   `pop`, `push_untracked`, `set_untracked` and the same entry points on
   `Vec` carried no inline attribute and were called out of line per element
   (only the get/set family was marked); the static parallel-store `try_push`
   likewise. Fixed in this branch with `#[inline(always)]`, the same fix that
   closed the earlier interning regression.

### Vec audit table (branch, after the inline attributes)

| function | instr | inner loop | verus calls | panic paths | carried | dup loads |
|---|---:|---:|---:|---:|---:|---:|
| `lvec_inline_tracked::probe_lvec_get` | 54 | 9 | 0 | 1 | 0 | 0 |
| `lvec_inline_tracked::probe_lvec_get_set` | 64 | 15 | 0 | 1 | 0 | 0 |
| `lvec_inline_tracked::probe_lvec_mark_set_restore` | 422 | 8 | 4 | 5 | 3 | 3 |
| `lvec_inline_tracked::probe_lvec_pop` | 96 | 17 | 1 | 1 | 0 | 0 |
| `lvec_inline_tracked::probe_lvec_push` | 96 | 22 | 1 | 1 | 0 | 0 |
| `lvec_inline_tracked::probe_lvec_set` | 61 | 8 | 0 | 1 | 0 | 0 |
| `lvec_inline_untracked::probe_lvec_get` | 99 | 9 | 1 | 1 | 0 | 0 |
| `lvec_inline_untracked::probe_lvec_get_set` | 110 | 11 | 1 | 2 | 0 | 0 |
| `lvec_inline_untracked::probe_lvec_pop` | 104 | 11 | 1 | 1 | 0 | 0 |
| `lvec_inline_untracked::probe_lvec_push` | 84 | 13 | 1 | 1 | 0 | 0 |
| `lvec_inline_untracked::probe_lvec_set` | 113 | 10 | 1 | 2 | 0 | 0 |
| `lvec_parallel_tracked::probe_lvec_get` | 97 | 8 | 0 | 1 | 0 | 0 |
| `lvec_parallel_tracked::probe_lvec_get_set` | 136 | 23 | 0 | 2 | 0 | 1 |
| `lvec_parallel_tracked::probe_lvec_mark_set_restore` | 597 | 8 | 4 | 5 | 3 | 3 |
| `lvec_parallel_tracked::probe_lvec_pop` | 117 | 20 | 0 | 1 | 1 | 0 |
| `lvec_parallel_tracked::probe_lvec_push` | 74 | None | 0 | 1 | 0 | 0 |
| `lvec_parallel_tracked::probe_lvec_set` | 137 | 21 | 0 | 3 | 0 | 0 |
| `lvec_parallel_untracked::probe_lvec_get` | 104 | 8 | 1 | 1 | 0 | 0 |
| `lvec_parallel_untracked::probe_lvec_get_set` | 114 | 8 | 1 | 2 | 0 | 0 |
| `lvec_parallel_untracked::probe_lvec_pop` | 109 | 8 | 1 | 1 | 0 | 0 |
| `lvec_parallel_untracked::probe_lvec_push` | 88 | 11 | 1 | 1 | 0 | 0 |
| `lvec_parallel_untracked::probe_lvec_set` | 180 | 8 | 1 | 2 | 0 | 0 |
| `svec_inline_tracked::probe_svec_get_index` | 121 | 9 | 0 | 1 | 0 | 0 |
| `svec_inline_tracked::probe_svec_mark_set_restore` | 255 | 11 | 5 | 6 | 1 | 3 |
| `svec_inline_tracked::probe_svec_pop` | 103 | 17 | 2 | 1 | 0 | 4 |
| `svec_inline_tracked::probe_svec_push` | 116 | 29 | 3 | 2 | 0 | 1 |
| `svec_inline_tracked::probe_svec_set_index` | 120 | 56 | 2 | 3 | 1 | 2 |
| `svec_inline_tracked::probe_svec_set_index_nodrop` | 91 | 26 | 1 | 4 | 1 | 1 |
| `svec_inline_untracked::probe_svec_get_index` | 121 | 9 | 0 | 1 | 0 | 0 |
| `svec_inline_untracked::probe_svec_pop` | 32 | None | 0 | 0 | 0 | 0 |
| `svec_inline_untracked::probe_svec_push` | 90 | 12 | 2 | 1 | 0 | 0 |
| `svec_inline_untracked::probe_svec_set_index` | 50 | 10 | 0 | 2 | 0 | 0 |
| `svec_inline_untracked::probe_svec_set_index_nodrop` | 38 | 10 | 0 | 2 | 0 | 0 |
| `svec_parallel_tracked::probe_svec_get_index` | 116 | 8 | 0 | 1 | 0 | 0 |
| `svec_parallel_tracked::probe_svec_mark_set_restore` | 291 | 15 | 7 | 6 | 1 | 6 |
| `svec_parallel_tracked::probe_svec_pop` | 146 | 94 | 4 | 1 | 2 | 6 |
| `svec_parallel_tracked::probe_svec_push` | 160 | 22 | 5 | 3 | 1 | 3 |
| `svec_parallel_tracked::probe_svec_set_index` | 150 | 85 | 4 | 3 | 1 | 5 |
| `svec_parallel_tracked::probe_svec_set_index_nodrop` | 103 | 32 | 2 | 4 | 1 | 3 |
| `svec_parallel_untracked::probe_svec_get_index` | 116 | 8 | 0 | 1 | 0 | 0 |
| `svec_parallel_untracked::probe_svec_pop` | 31 | None | 0 | 0 | 0 | 0 |
| `svec_parallel_untracked::probe_svec_push` | 114 | 12 | 2 | 2 | 0 | 0 |
| `svec_parallel_untracked::probe_svec_set_index` | 48 | 8 | 0 | 2 | 0 | 0 |
| `svec_parallel_untracked::probe_svec_set_index_nodrop` | 36 | 8 | 0 | 2 | 0 | 0 |
| `vec_inline_tracked::probe_vec_as_slice_sum` | 120 | 8 | 0 | 0 | 0 | 0 |
| `vec_inline_tracked::probe_vec_get_index` | 72 | 8 | 0 | 1 | 0 | 0 |
| `vec_inline_tracked::probe_vec_get_set` | 262 | 80 | 7 | 2 | 3 | 9 |
| `vec_inline_tracked::probe_vec_mark_pop_scope` | 337 | 48 | 9 | 5 | 1 | 4 |
| `vec_inline_tracked::probe_vec_mark_push_restore_and_pop` | 286 | 30 | 9 | 5 | 2 | 4 |
| `vec_inline_tracked::probe_vec_mark_set_restore` | 367 | 15 | 10 | 5 | 2 | 10 |
| `vec_inline_tracked::probe_vec_nested_marks` | 497 | 27 | 13 | 6 | 4 | 9 |
| `vec_inline_tracked::probe_vec_pop` | 239 | 63 | 7 | 1 | 5 | 10 |
| `vec_inline_tracked::probe_vec_push` | 205 | 29 | 7 | 3 | 2 | 4 |
| `vec_inline_tracked::probe_vec_push_untracked` | 219 | 32 | 7 | 3 | 2 | 7 |
| `vec_inline_tracked::probe_vec_set_index` | 272 | 26 | 7 | 3 | 3 | 9 |
| `vec_inline_tracked::probe_vec_set_untracked` | 285 | 29 | 7 | 3 | 3 | 13 |
| `vec_inline_tracked::probe_vec_try_extend` | 551 | 23 | 28 | 3 | 1 | 3 |
| `vec_inline_untracked::probe_vec_as_slice_sum` | 120 | 8 | 0 | 0 | 0 | 0 |
| `vec_inline_untracked::probe_vec_get_index` | 72 | 8 | 0 | 1 | 0 | 0 |
| `vec_inline_untracked::probe_vec_get_set` | 76 | 9 | 0 | 1 | 0 | 0 |
| `vec_inline_untracked::probe_vec_pop` | 72 | None | 0 | 0 | 0 | 0 |
| `vec_inline_untracked::probe_vec_push` | 147 | 20 | 3 | 2 | 2 | 2 |
| `vec_inline_untracked::probe_vec_push_untracked` | 170 | 26 | 3 | 2 | 2 | 5 |
| `vec_inline_untracked::probe_vec_set_index` | 96 | 8 | 0 | 2 | 0 | 0 |
| `vec_inline_untracked::probe_vec_set_untracked` | 129 | 8 | 0 | 2 | 0 | 0 |
| `vec_inline_untracked::probe_vec_try_extend` | 382 | 88 | 24 | 2 | 2 | 2 |
| `vec_parallel_tracked::probe_vec_as_slice_sum` | 120 | 8 | 0 | 0 | 0 | 0 |
| `vec_parallel_tracked::probe_vec_get_index` | 72 | 8 | 0 | 1 | 0 | 0 |
| `vec_parallel_tracked::probe_vec_get_set` | 262 | 80 | 7 | 2 | 3 | 9 |
| `vec_parallel_tracked::probe_vec_mark_pop_scope` | 337 | 48 | 9 | 5 | 1 | 4 |
| `vec_parallel_tracked::probe_vec_mark_push_restore_and_pop` | 286 | 30 | 9 | 5 | 2 | 4 |
| `vec_parallel_tracked::probe_vec_mark_set_restore` | 367 | 15 | 10 | 5 | 2 | 10 |
| `vec_parallel_tracked::probe_vec_nested_marks` | 497 | 27 | 13 | 6 | 4 | 9 |
| `vec_parallel_tracked::probe_vec_pop` | 239 | 63 | 7 | 1 | 5 | 10 |
| `vec_parallel_tracked::probe_vec_push` | 206 | 19 | 7 | 3 | 2 | 4 |
| `vec_parallel_tracked::probe_vec_push_untracked` | 220 | 20 | 7 | 3 | 2 | 7 |
| `vec_parallel_tracked::probe_vec_set_index` | 272 | 26 | 7 | 3 | 3 | 9 |
| `vec_parallel_tracked::probe_vec_set_untracked` | 285 | 29 | 7 | 3 | 3 | 13 |
| `vec_parallel_tracked::probe_vec_try_extend` | 552 | 23 | 28 | 3 | 1 | 3 |
| `vec_parallel_untracked::probe_vec_as_slice_sum` | 120 | 8 | 0 | 0 | 0 | 0 |
| `vec_parallel_untracked::probe_vec_get_index` | 72 | 8 | 0 | 1 | 0 | 0 |
| `vec_parallel_untracked::probe_vec_get_set` | 76 | 9 | 0 | 1 | 0 | 0 |
| `vec_parallel_untracked::probe_vec_pop` | 72 | None | 0 | 0 | 0 | 0 |
| `vec_parallel_untracked::probe_vec_push` | 149 | 18 | 3 | 2 | 2 | 2 |
| `vec_parallel_untracked::probe_vec_push_untracked` | 172 | 20 | 3 | 2 | 2 | 5 |
| `vec_parallel_untracked::probe_vec_set_index` | 96 | 8 | 0 | 2 | 0 | 0 |
| `vec_parallel_untracked::probe_vec_set_untracked` | 129 | 8 | 0 | 2 | 0 | 0 |
| `vec_parallel_untracked::probe_vec_try_extend` | 384 | 20 | 24 | 2 | 2 | 2 |
| `vec_trail_tracked::probe_vec_as_slice_sum` | 120 | 8 | 0 | 0 | 0 | 0 |
| `vec_trail_tracked::probe_vec_get_index` | 72 | 8 | 0 | 1 | 0 | 0 |
| `vec_trail_tracked::probe_vec_get_set` | 262 | 80 | 7 | 2 | 3 | 9 |
| `vec_trail_tracked::probe_vec_mark_pop_scope` | 337 | 48 | 9 | 5 | 1 | 4 |
| `vec_trail_tracked::probe_vec_mark_push_restore_and_pop` | 286 | 30 | 9 | 5 | 2 | 4 |
| `vec_trail_tracked::probe_vec_mark_set_restore` | 367 | 15 | 10 | 5 | 2 | 10 |
| `vec_trail_tracked::probe_vec_nested_marks` | 497 | 27 | 13 | 6 | 4 | 9 |
| `vec_trail_tracked::probe_vec_pop` | 239 | 63 | 7 | 1 | 5 | 10 |
| `vec_trail_tracked::probe_vec_push` | 205 | 29 | 7 | 3 | 2 | 4 |
| `vec_trail_tracked::probe_vec_push_untracked` | 219 | 32 | 7 | 3 | 2 | 7 |
| `vec_trail_tracked::probe_vec_set_index` | 272 | 26 | 7 | 3 | 3 | 9 |
| `vec_trail_tracked::probe_vec_set_untracked` | 285 | 29 | 7 | 3 | 3 | 13 |
| `vec_trail_tracked::probe_vec_try_extend` | 551 | 20 | 28 | 3 | 1 | 3 |
| `vec_trail_untracked::probe_vec_as_slice_sum` | 120 | 8 | 0 | 0 | 0 | 0 |
| `vec_trail_untracked::probe_vec_get_index` | 72 | 8 | 0 | 1 | 0 | 0 |
| `vec_trail_untracked::probe_vec_get_set` | 76 | 9 | 0 | 1 | 0 | 0 |
| `vec_trail_untracked::probe_vec_pop` | 72 | None | 0 | 0 | 0 | 0 |
| `vec_trail_untracked::probe_vec_push` | 148 | 20 | 3 | 2 | 2 | 2 |
| `vec_trail_untracked::probe_vec_push_untracked` | 171 | 26 | 3 | 2 | 2 | 5 |
| `vec_trail_untracked::probe_vec_set_index` | 96 | 8 | 0 | 2 | 0 | 0 |
| `vec_trail_untracked::probe_vec_set_untracked` | 129 | 8 | 0 | 2 | 0 | 0 |
| `vec_trail_untracked::probe_vec_try_extend` | 383 | 88 | 24 | 2 | 2 | 2 |

## Findings on the composites

- **AppendOnlyVec**: parity or better in every row (verified 49 to 141
  instructions against legacy 64 to 202, same 8 to 11 loops).
- **SpMap / SpUniqueMap**: parity with legacy `Map` on intern and lookup
  (8 to 11 loops); the hasher seed resolution is one call per construction.
- **ListArena**: untracked append 37 versus 39, prepend 28 versus 30, iterate
  8 versus 8, splice 48 versus 9 (a splice-path inlining difference worth a
  look); tracked append 11 versus 10 but through an out-of-line `try_append`.
  The earlier benchmark regression on tracked-off append (0.79x against
  mainline) is a separate, diagnosed item: see below.
- **SparseSet**: add and contains at parity; tracked `set` with no frame open
  110 versus legacy 42, the same pattern as `Vec` since it is a `Vec` write.
- **UnionFind**: comparable loops; the verified `find` and `union` are called
  out of line in the e-classes probes.
- **EClasses**: `try_add_singleton`, `add_use`, `find` and `merge_with` are
  out-of-line calls in every probe (legacy inlines them); loop sizes are
  otherwise comparable (merge 15 versus 15).
- **BPlusTreeSet**: `try_insert` out of line on the verified side (legacy
  inlines it, 37-instruction probe); contains at parity.
- **CircularList**: `splice_core` and `guard_different_rings` out of line.

Out-of-line hot calls seen across both probes, by frequency:

- `History::pop_member::7vec_dyn::VecD::codegen_probe` (x6)
- `History::restore_and_pop_member::7vec_dyn::VecD::codegen_probe` (x6)
- `hasher_spec::resolve_default_seed` (x5)
- `StoredVElem::VElem::14para::ParallelStore::try_add` (x5)
- `codegen_probe_composites::StoredVElem::VElem::6NoJu::union_core` (x5)
- `codegen_probe_composites::StoredVElem::VElem::6NoJu::find` (x4)
- `StoredVRingKey::VRingKey::StoredVRingNode::VRingNode::guard_different_rings` (x4)
- `History::restore_member::7vec_dyn::VecD::codegen_probe` (x3)
- `codegen_probe_composites::StoredVElem::VElem::INtNtB7_12inline_::InlineStore` (x3)
- `StoredVId::VId::12bplus::Layout256U32::try_insert` (x2)
- `12bplus::Layout256U32::12bplus::BinarySearch::try_insert` (x2)
- `StoredVL::StoredVN::10union::NoJust::merge_with` (x2)
- `codegen_probe_composites::StoredVK::8StoredVE2VEEmINtNtB7_12in::InlineStore::mEE25runtime_appl` (x2)
- `StoredVElem::VElem::12inlin::InlineStore::mEE25runtime_appl` (x2)
- `codegen_probe_composites::StoredVK::8StoredVE2VEEmINtNtB7_12in::InlineStore::mEE19runtime_migr` (x2)
- `NoJust::12inline::InlineStore::mEE18runtime_push_::codegen_probe_composites` (x2)
- `StoredVNode::VNode::12inlin::InlineStore::mEE25runtime_appl` (x2)
- `StoredVNode::VNode::12inlin::InlineStore::mEE19runtime_migr` (x2)
- `StoredVList::VList::StoredVNode::VNode::try_append` (x2)
- `map::5SpMa::try_insert::codegen_probe_composites` (x2)
- `StoredVRingKey::VRingKey::StoredVRingNode::VRingNode::splice_core` (x2)
- `StoredVElem::VElem::14paral::ParallelStore::with_store` (x2)
- `StoredVElem::VElem::14para::ParallelStore::remove` (x2)
- `StoredVL::StoredVN::10union::NoJust::try_add_singleton` (x1)
- `StoredVL::StoredVN::10union::NoJust::add_use` (x1)
- `StoredVL::StoredVE::12inlin::InlineStore::mEE25runtime_appl` (x1)
- `codegen_probe_composites::StoredVE::14paral::ParallelStore::jEE25runtime_appl` (x1)
- `StoredVL::StoredVE::12inlin::InlineStore::mEE19runtime_migr` (x1)
- `codegen_probe_composites::StoredVE::14paral::ParallelStore::jEE19runtime_migr` (x1)
- `StoredVNode::VNode::12inlin::InlineStore::mEE26reconstruct_` (x1)
- `NtC::history::7Hist::restore_and_pop` (x1)
- `codegen_probe_composites::StoredVElem::VElem::14paral::ParallelStore` (x1)
- `codegen_probe_composites::StoredVElem::VElem::INtNtB8_12inline_s::InlineStore` (x1)
- `StoredVElem::VElem::12inlin::InlineStore::mEE26reconstruct_` (x1)
- `NoJust::12inlin::InlineStore::mEE21runtime_rest::codegen_probe_composites` (x1)

### Composite audit table

| function | instr | inner loop | verus calls | panic paths | carried | dup loads |
|---|---:|---:|---:|---:|---:|---:|
| `aov_tracked::probe_aov_get_p` | 114 | 8 | 1 | 0 | 0 | 0 |
| `aov_tracked::probe_aov_get_v` | 101 | 8 | 1 | 0 | 0 | 0 |
| `aov_tracked::probe_aov_iter_p` | 81 | 8 | 1 | 0 | 0 | 0 |
| `aov_tracked::probe_aov_iter_v` | 68 | 8 | 1 | 0 | 0 | 0 |
| `aov_tracked::probe_aov_mark_push_restore_p` | 202 | 10 | 1 | 3 | 0 | 0 |
| `aov_tracked::probe_aov_mark_push_restore_v` | 141 | 11 | 2 | 1 | 0 | 0 |
| `aov_tracked::probe_aov_push_p` | 64 | 9 | 1 | 0 | 0 | 0 |
| `aov_tracked::probe_aov_push_v` | 49 | 9 | 1 | 0 | 0 | 0 |
| `bplus_tracked::probe_bplus_contains_p` | 247 | 8 | 0 | 3 | 0 | 1 |
| `bplus_tracked::probe_bplus_contains_v` | 224 | 10 | 2 | 3 | 0 | 0 |
| `bplus_tracked::probe_bplus_insert_p` | 37 | None | 0 | 0 | 0 | 0 |
| `bplus_tracked::probe_bplus_insert_v` | 62 | 8 | 2 | 1 | 0 | 0 |
| `bplus_untracked::probe_bplus_contains_p` | 247 | 8 | 0 | 3 | 0 | 1 |
| `bplus_untracked::probe_bplus_contains_v` | 224 | 10 | 2 | 3 | 0 | 0 |
| `bplus_untracked::probe_bplus_insert_p` | 37 | None | 0 | 0 | 0 | 0 |
| `bplus_untracked::probe_bplus_insert_v` | 62 | 8 | 2 | 1 | 0 | 0 |
| `eclasses_tracked::probe_ec_add_singleton_use_p` | 193 | 13 | 0 | 1 | 0 | 0 |
| `eclasses_tracked::probe_ec_add_singleton_use_v` | 72 | 9 | 3 | 1 | 0 | 0 |
| `eclasses_tracked::probe_ec_find_p` | 135 | 8 | 1 | 2 | 1 | 0 |
| `eclasses_tracked::probe_ec_find_v` | 65 | 10 | 1 | 1 | 0 | 0 |
| `eclasses_tracked::probe_ec_mark_merge_restore_p` | 1834 | 8 | 9 | 12 | 8 | 5 |
| `eclasses_tracked::probe_ec_mark_merge_restore_v` | 1038 | 9 | 46 | 6 | 10 | 19 |
| `eclasses_tracked::probe_ec_merge_p` | 77 | 15 | 0 | 1 | 0 | 0 |
| `eclasses_tracked::probe_ec_merge_v` | 80 | 15 | 1 | 1 | 0 | 0 |
| `list_tracked::probe_list_append_p` | 91 | 10 | 1 | 2 | 0 | 0 |
| `list_tracked::probe_list_append_v` | 109 | 11 | 4 | 2 | 0 | 0 |
| `list_tracked::probe_list_iter_p` | 83 | 8 | 0 | 1 | 0 | 0 |
| `list_tracked::probe_list_iter_v` | 84 | 8 | 0 | 1 | 0 | 0 |
| `list_tracked::probe_list_mark_append_restore_p` | 640 | 8 | 4 | 7 | 2 | 1 |
| `list_tracked::probe_list_mark_append_restore_v` | 1051 | 9 | 43 | 9 | 9 | 6 |
| `list_tracked::probe_list_prepend_p` | 153 | 43 | 2 | 3 | 1 | 0 |
| `list_tracked::probe_list_prepend_v` | 233 | 18 | 7 | 3 | 5 | 4 |
| `list_tracked::probe_list_splice_p` | 168 | 13 | 0 | 3 | 0 | 2 |
| `list_tracked::probe_list_splice_v` | 397 | 10 | 8 | 2 | 6 | 11 |
| `list_untracked::probe_list_append_p` | 148 | 39 | 2 | 4 | 1 | 0 |
| `list_untracked::probe_list_append_v` | 122 | 37 | 3 | 3 | 1 | 0 |
| `list_untracked::probe_list_iter_p` | 83 | 8 | 0 | 1 | 0 | 0 |
| `list_untracked::probe_list_iter_v` | 84 | 8 | 0 | 1 | 0 | 0 |
| `list_untracked::probe_list_prepend_p` | 126 | 30 | 2 | 2 | 1 | 0 |
| `list_untracked::probe_list_prepend_v` | 111 | 28 | 3 | 2 | 1 | 0 |
| `list_untracked::probe_list_splice_p` | 262 | 9 | 0 | 3 | 0 | 0 |
| `list_untracked::probe_list_splice_v` | 143 | 48 | 0 | 2 | 0 | 0 |
| `map_tracked::probe_map_intern_p` | 179 | 11 | 0 | 1 | 0 | 0 |
| `map_tracked::probe_map_intern_unique_v` | 199 | 8 | 2 | 1 | 0 | 0 |
| `map_tracked::probe_map_intern_v` | 208 | 8 | 2 | 2 | 0 | 0 |
| `map_tracked::probe_map_lookup_p` | 228 | 11 | 0 | 2 | 1 | 0 |
| `map_tracked::probe_map_lookup_v` | 201 | 11 | 2 | 2 | 0 | 0 |
| `map_tracked::probe_map_mark_insert_restore_p` | 506 | 10 | 0 | 5 | 1 | 0 |
| `map_tracked::probe_map_mark_insert_restore_v` | 622 | 8 | 7 | 7 | 0 | 0 |
| `map_untracked::probe_map_intern_p` | 179 | 11 | 0 | 1 | 0 | 0 |
| `map_untracked::probe_map_lookup_p` | 228 | 11 | 0 | 2 | 1 | 0 |
| `map_untracked::probe_map_lookup_v` | 325 | 8 | 2 | 3 | 0 | 0 |
| `ring_tracked::probe_ring_add_splice_v` | 121 | 36 | 6 | 1 | 1 | 1 |
| `ring_tracked::probe_ring_walk_v` | 146 | 36 | 6 | 2 | 1 | 1 |
| `ring_untracked::probe_ring_add_splice_v` | 117 | 29 | 4 | 1 | 0 | 1 |
| `ring_untracked::probe_ring_walk_v` | 117 | 26 | 4 | 1 | 0 | 1 |
| `sparse_tracked::probe_sparse_add_p` | 66 | None | 0 | 0 | 0 | 0 |
| `sparse_tracked::probe_sparse_add_v` | 62 | 8 | 2 | 1 | 0 | 0 |
| `sparse_tracked::probe_sparse_contains_get_p` | 110 | 10 | 0 | 2 | 0 | 0 |
| `sparse_tracked::probe_sparse_contains_get_v` | 110 | 9 | 0 | 3 | 0 | 0 |
| `sparse_tracked::probe_sparse_mark_churn_restore_p` | 491 | 8 | 2 | 6 | 2 | 3 |
| `sparse_tracked::probe_sparse_mark_churn_restore_v` | 648 | 9 | 13 | 9 | 0 | 0 |
| `sparse_tracked::probe_sparse_remove_add_p` | 65 | 13 | 0 | 1 | 0 | 0 |
| `sparse_tracked::probe_sparse_remove_add_v` | 84 | 15 | 2 | 2 | 0 | 0 |
| `sparse_tracked::probe_sparse_set_p` | 125 | 42 | 0 | 3 | 0 | 1 |
| `sparse_tracked::probe_sparse_set_v` | 206 | 110 | 2 | 5 | 1 | 6 |
| `sparse_untracked::probe_sparse_add_p` | 66 | None | 0 | 0 | 0 | 0 |
| `sparse_untracked::probe_sparse_add_v` | 62 | 8 | 2 | 1 | 0 | 0 |
| `sparse_untracked::probe_sparse_contains_get_p` | 110 | 10 | 0 | 2 | 0 | 0 |
| `sparse_untracked::probe_sparse_contains_get_v` | 110 | 9 | 0 | 3 | 0 | 0 |
| `sparse_untracked::probe_sparse_remove_add_p` | 134 | 14 | 0 | 3 | 1 | 0 |
| `sparse_untracked::probe_sparse_remove_add_v` | 151 | 19 | 1 | 4 | 1 | 0 |
| `sparse_untracked::probe_sparse_set_p` | 110 | 22 | 0 | 3 | 0 | 0 |
| `sparse_untracked::probe_sparse_set_v` | 117 | 21 | 0 | 3 | 0 | 0 |
| `uf_tracked::probe_uf_find_const_p` | 98 | 8 | 0 | 1 | 0 | 0 |
| `uf_tracked::probe_uf_find_const_v` | 118 | 12 | 1 | 5 | 0 | 0 |
| `uf_tracked::probe_uf_mark_union_restore_p` | 230 | 8 | 1 | 2 | 1 | 2 |
| `uf_tracked::probe_uf_mark_union_restore_v` | 843 | 9 | 17 | 12 | 3 | 1 |
| `uf_tracked::probe_uf_union_find_p` | 155 | 8 | 1 | 2 | 1 | 0 |
| `uf_tracked::probe_uf_union_find_v` | 84 | 21 | 2 | 3 | 0 | 0 |
| `uf_untracked::probe_uf_find_const_p` | 98 | 8 | 0 | 1 | 0 | 0 |
| `uf_untracked::probe_uf_find_const_v` | 118 | 12 | 1 | 5 | 0 | 0 |
| `uf_untracked::probe_uf_union_find_p` | 158 | 9 | 0 | 2 | 0 | 0 |
| `uf_untracked::probe_uf_union_find_v` | 136 | 14 | 2 | 5 | 0 | 1 |

## The systemic cause, and what was ruled out

The tracked-write reloads and the list-append regression share one
mechanism: values that live in the container's stack frame (lengths,
pointers, watermarks, head fields) are re-read every iteration instead of
being carried in registers, even though nothing in the loop can change them.
Ruled out with evidence, in order: an un-inlined method (removing the call
changed nothing), a stack-carried loop counter (removing it changed nothing
in time), drop glue capturing the container (forgetting it changed nothing),
the container's address escaping (every callee that receives it is
`captures(none)`, no address is ever stored), loop size against LLVM's
threshold (doubling it changed nothing). What does work, mechanically:
forcing LLVM to peel one loop iteration restores the mainline code exactly,
and mainline's early full-unroll pass peels this loop on its own while the
branch's does not. A hand-inspection of the pre-unroll IR shows the branch
loop reaching that pass with its head fields still loaded from memory, so the
peel heuristic sees nothing to specialise. Why the earlier passes leave them
in memory on the branch and not on mainline is the open question; no `opt`
matching rustc's LLVM 22 is installed here to print MemorySSA's view.

## Fix list

| # | change | status |
|---|---|---|
| F1 | `#[inline(always)]` on `VecD` forwarders and `Vec` per-element entry points | applied (design ch.20 H1); `try_extend` excluded, see below |
| F2 | reorder `try_append`: read the node count before the heads bounds check | applied earlier, removed the carried slot, no time change; kept for the codegen it buys |
| F3 | tracked writes: one executable write path (design ch.20 H6), checked accessors `get_at`/`set_at` (H4) | applied and measured, see below |
| F4 | `#[inline]` on the composite hot methods LLVM declined (`EClasses::{add_use, find, try_add_singleton}`, `SparseSet::{try_add, remove}`, `ListArena::try_append`, `CircularList::{splice_core, guard_different_rings}`) | proposed; measure, since call overhead may be minor relative to the bodies |
| F5 | list append regression: make the early peel fire | done: store length reads return the slice length (no `Vec::len` assume); see below |

Every fix is validated first by the audit (the loop shape must change) and
then by the paired benchmark protocol (`tools/bench_compare.py`, tau 1.08,
two interleaved rounds, mainline as the reference), before the gate.

## F3 result: one tracked write path (2026-09-22)

The Hot projection arms (`hot_defer_push_checked`, `hot_defer_set_checked`,
`hot_defer_pop_checked` and their two capture helpers, 757 lines) are deleted;
`runtime_push`/`runtime_set`/`runtime_pop` call the general path
unconditionally, whose lemmas needed only `wf` plus the effect predicates.
`get_index`/`set_index` stay total and delegate to `get_at`/`set_at`, whose
bound is a precondition. `hot_defer_scope_exec` tests `TRACK` before any read.

Audit, reference = the tree before the change (`0cd65bc`), same probes:

| probe (tracked, no frame open) | instr | inner loop | dup loads |
|---|---|---|---|
| `vec_*::probe_vec_set_index` | 268 → 218 | 83 → 59 | 10 → 5 |
| `vec_*::probe_vec_get_set` | 235 → 189 | 87 → 59 | 10 → 5 |
| `svec_parallel::probe_svec_set_index` | 151 → 117 | 85 → 51 | 5 → 3 |
| `svec_parallel::probe_svec_pop` | 146 → 107 | 94 → 53 | 6 → 3 |
| `svec_inline::probe_svec_set_index` | 123 → 106 | 56 → 39 | 2 → 1 |

Rows whose instruction count *rose* (`VecD` push/pop/set_untracked/try_extend,
`svec_parallel::probe_svec_push` 99 → 138) are the F1 inline attributes taking
effect: the reference loop was a call per element and the new loop is the same
work inlined with no call (verified on the parallel push disassembly: eight
instructions around a `bl try_push` became an eighteen-instruction body with
the length check, the capacity check, the store and the watermark compare).
The exception is `try_extend`, whose `VecD` probe went from 107 to 622
instructions with 24 out-of-line calls once inlined; it is a batch operation,
not a per-element path, so the attribute is not applied there.

Paired benchmark, reference = `0cd65bc`, two interleaved rounds, speedup =
reference ÷ new (legacy arm in brackets as the placement canary):

| row | round A | round B |
|---|---|---|
| `sparse_set/churn/verified` | 1.10× [1.00] | 1.11× [1.01] |
| `class_ring/merge_restore/verified` | 1.07× [1.00] | 1.07× [1.00] |
| `vec/mark_set_restore/verified` | 1.07× [1.05] | 1.05× [1.05] |
| `active_frame_write/*` (six rows) | 0.98–1.02× | 1.00–1.05× |
| `tracked_veci/mark_churn/verus/{1000,100000}` | 1.02–1.03× | 1.02–1.03× |
| `list/append_iter/verified` | 1.01× [1.00] | 0.99× [0.99] |
| `map/intern/verified` | 0.96–0.98× [1.01–1.02] | 0.96–0.98× [1.02–1.05] |
| `vec/try_extend/verified` | 0.89–0.99× [1.03–1.10] | 0.88–0.95× [0.94–1.03] |

The two bottom rows were re-run twice; the legacy canary moved by up to ten
per cent between rounds each time, so those rounds are discarded under the
protocol. `vec/try_extend/verified` runs with tracking off, where the change
touches no executable statement (the untracked static probe rows are
identical in the audit), so its swing is placement. The `map/intern` deficit
of two to four per cent sits inside tau with overlapping intervals and is
carried as a watch item for the SparseSet/SpMap work (item 2).

## Item 2 result: SparseSet lookup reuse (2026-09-22)

`SparseSet::lookup` reads the sparse length, the sparse slot, the dense
length and the indices slot once and returns the validated dense position;
`contains`, `get`, `set`, `remove` and `try_get` consume it, and every
internal read and write inside `add`, `remove` and `remove_value` uses the
checked accessors. Verified 30/0 unchanged in contract.

Audit vs the item 1 commit (`350e1e1`): no loop-shape change. The tracked
`set` probe stays at 75 inner instructions; `contains_get` gains six
instructions outside the loop. LLVM was already merging the repeated loads,
since no store separates a `contains` from the position read that follows
it. The measured effect is parity, reported as such:

| row | round A | round B |
|---|---|---|
| `sparse_set/churn/verified` | 1.01× [1.01] | 1.01× [0.99] |
| `eclasses/merge_cascade/verified` | 1.03× [1.00] | 0.99× [0.99] |
| `eclasses/mark_merge_restore/verified` | 0.99× | 1.00× |
| `compress_columns/sequential/*` (15 rows) | 0.99–1.01× | 0.98–1.03× |

One lesson worth the record. The first form of this change regressed
`eclasses/merge_cascade/verified` to 0.88–0.91× in every round while the
retained canary held at 1.00×, and a control run with the file restored to
HEAD was at parity, so the source was responsible. Bisection: the inline
attributes on `lookup`/`contains` were not it; `remove` on the bool test was
not it; reverting `get_live`/`set_live` to the public checked accessors
recovered the row. The two bodies had become smaller (no bound branch), and
that changed LLVM's inlining decisions inside the e-class merge functions
that call them, a heuristic cascade of exactly the kind the governing
principle warns about. Demonstrated on the e-class bench binaries: the
regressed build carries an out-of-line `SparseSet::set_live` (420 bytes,
called once per merge with the class record passed by value) and its
`EClasses` merge body is 2864 bytes; the reference and the fixed build have
no out-of-line sparse-set symbol at all and merge bodies of 3148 and 3324
bytes. The symbol tables, not the probes, show the change, which is why the
isolated audit missed it: the probe loops are small enough that the accessor
inlines there regardless. Marking `get_live`/`set_live` `#[inline(always)]`
(they are per-element paths, so the H1 rule applies) restores parity with
the checked accessors kept. Rule confirmed from the other side: shrinking a
per-element callee without pinning its inlining is a change to the caller's
codegen, and it must be measured.

## Item 3 result: list check-once (2026-09-22)

`ListArena::append`/`prepend` (crate-internal) no longer call
`check_precondition` on the id-range facts their `requires` already carry;
`append_raw`/`prepend_raw` read and write heads and nodes through the checked
accessors; `try_append` reads the node count before the heads bounds check.
Verified 77/0; partial-API gate unchanged (the public `try_append`/
`try_prepend` keep their explicit checks).

Measured effect on the peel: none. The closure keeps its two unpeeled inner
loops (52 and 67 instructions against mainline's 43 and 53), and the paired
rows read (speedup = reference ÷ new, two rounds):

| reference | `list/append_iter/verified` | `list/splice/verified` |
|---|---|---|
| previous commit `72eb850` | 1.02× / 1.00× | 1.03× / 1.01× |
| upstream main `8f60f49` (post-merge) | 1.00× / 1.00× | 1.04× / 1.04× |
| pre-merge mainline `85e9de3` | **0.80× / 0.80×** (160 µs vs 200 µs) | 1.07× / 1.07× |

So H7's open question is answered in the negative: removing the re-check and
the extra length reads from the list layer does not hand LLVM the peel. The
trigger sits below the list layer, in the vector code the merge changed, and
stays open (F5). Note that `sp-ref-main` is upstream main *after* the merge
and measures identical to this branch; the 0.79× row exists only against the
pre-merge tree.

## F5 result: the list-append peel (2026-09-22)

**Bisection.** Oracle: the append benchmark's verified-to-legacy time ratio
in one process (immune to core placement; 0.79 on the pre-merge mainline,
0.99 on the branch). First bad commit over the 126 merged commits: 7ece790,
"GenStamps fork-history reclamation". It touched no executable statement of
the list layer.

**Mechanism, from the per-pass IR of the benchmark closure on both sides of
that commit** (traces and the parsing scripts are kept in the session
scratchpad; the chapter 20 H7 section carries the reasoning):

1. The peel is LLVM's early full-unroll pass acting on a loop-header phi that
   becomes invariant after the first iteration. Mainline's append loop header
   carries `phi i1 [l < heads.len, entry], [true, latch]`.
2. That phi is InstCombine's fold of a compare of a phi into a phi of
   compares, which requires the phi to have one use. The branch's phi of the
   heads length had two: the compare, and the `llvm.assume(len <= isize::MAX
   / size_of::<T>())` that std's `Vec::len` attaches to its result.
3. The assume folds only when the phi's range is known. Mainline entered the
   loop with the constant 2000: the benchmark closure was optimized as its
   own function first, and its GVN seeded the length from the constructor's
   visible `len = 0` store. 7ece790 grew `Vec::with_store` (a `GenStamps::new`
   loop) past the early inliner's budget, `ListArena::new` became an opaque
   call, the seed became a load of unknown range, the assume survived, no
   fold, no peel. On the current tree the closure is merged into the criterion
   driver before any GVN runs, so restoring the constructor's visibility alone
   does not help (measured, no change).
4. Fix in the library's hands: read lengths as the slice length. Same value,
   no assume, one use, the fold fires whatever the entry value's range is.

**Measured** (speedup = reference ÷ new; two interleaved rounds):

| measurement | before | after |
|---|---|---|
| peel oracle, verified ÷ legacy | 0.99 | 0.84 (mainline 0.79) |
| `list/append_iter/verified` vs pre-merge 85e9de3 | 0.80× | 0.92× (200 µs → 170 µs; legacy arm 200 µs both times) |
| `list/splice/verified` vs 85e9de3 | 1.07× | 1.05× / 1.08× |
| closure inner loop | 52 instr, unpeeled | 38 instr, peeled (mainline 37) |
| `probe_svec_get_index` (all stores) | 116–121 instr | 40–41 instr |
| broad set vs previous commit (73 rows) | | 63 pass, 10 inconclusive by reference drift, 0 regressions |

**Ruled out by one measurement each:** inlining the whole constructor chain
(`ListArena::new`, `with_store*`, `GenStamps::new`, `env_compress_default`;
ratio 0.986), writing the head record before the node push (1.095, worse),
raising GVN's memdep scan limits to 2000/5000 (1.007), a config-read barrier
(no atomic load in the loop). Forced peeling (`-unroll-force-peel-count=1`)
takes the legacy arm to the same 160 µs as the verified arm, so the entire
mainline-versus-legacy advantage was the peel.

**Remaining 8 per cent.** The steady-state loops now differ by one
instruction pair: our loop keeps the std bounds check on the old tail's node
read (`nodes.get_at` → `data[i]`), which mainline's explicit `get_index`
pre-check let LLVM fold. Removing it needs an unchecked read, which the trust
policy excludes; it stays as measured.

## Wave 1 (2026-09-23): the harness

**Opaque-input variants** (8444bd1) beside the fixed rows: `list/append_iter_opaque`,
`list/splice_opaque`, `sparse_set/churn_opaque`, `eclasses/merge_cascade_opaque`.
One plan per group from the seeded `Rng`, laundered through `black_box` once,
shared by both arms; the fixed rows' loop nests with runtime trip counts.

Check G, same process, mean times:

| row | 4cb5f1b legacy / verified | cb54a69 legacy / verified |
|---|---|---|
| append_iter (fixed) | 199.3 / 168.3 µs (0.84) | 199.9 / 202.6 µs (1.01) |
| append_iter_opaque | 217.5 / 217.0 µs (1.00) | 219.0 / 216.8 µs (0.99) |
| churn_opaque | 358.4 / 277.9 µs (0.78) | 358.1 / 280.9 µs (0.78) |
| merge_cascade_opaque | 152.7 / 101.4 µs | 151.5 / 96.9 µs |

The opaque append does not reproduce the fixed row's sign, and the reason is
found: the peel is LLVM's early full-unroll pass, which acts only on a loop
whose trip count is a compile-time constant. With a runtime count neither
arm is peeled and the verified append is at parity with legacy on both trees.
So 3c33709's gain is real for constant-count callers and neutral otherwise;
H7's mechanism stands, its reach is narrower than the fixed row suggested.
Two plan shapes were rejected by measurement before this one: a random list
order (memory-bound; the unchanged legacy arm moved 30 per cent between
builds) and a flat op sequence (no loop nest, nothing to peel, both arms
244 µs).

**Coverage** (eb3e16c): `bplus/cursor_seek_sequential` (prod and verus,
tracked and untracked), `map/intern_expensive_key`, `two_stack/long_run`
(zero-frame flush and hot-4 rows), `eclasses/set_min_monomial`,
`union_find/explain_deep_chain`. First numbers: the B+ sequential seek is
4.4× on the verified side (980 vs 221 µs untracked, 955 vs 196 tracked),
which is item 6's missing current-leaf fast path measured; the other four
are at parity before their changes.

Reopened as questions, not closed: the attribution of the last 8 per cent on
the fixed append row to the tail-node bounds check (needs the single-variable
measurement), and whether the five `loop { invariant false }` arms can go
(only `unreached()` was measured, and it was slower).

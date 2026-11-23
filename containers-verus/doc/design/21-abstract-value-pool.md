<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# 21. The Abstract-Value Pool

[← 20 Hot-Path Discipline](20-hot-path-discipline.md) · [Table of contents](00-table-of-contents.md)

This chapter describes how the class layer stores one abstract value per
e-class. §7 records the design decisions and where the implementation departs
from the API sketched in §2.

## 1. What the pool provides

The class layer gives every e-class an optional abstract value stored in the class
layer. The class layer is `containers-verus/src/eclasses.rs`, and
`egraph::EClasses` and `egraph::UnionFind` are type aliases of it. The
design follows the storage proposal in
[eclass-analysis.md §4](../../../egraph/doc/future/eclass-analysis.md#4-storage):
a handle in `ClassData`, values in a pool under the same mark.

It consists of five parts:

1. a field `abs` in `ClassData`, a handle into a new abstract-value pool;
2. the pool itself, a semi-persistent vector of opaque fixed-width `Copy`
   entries, marked and restored with the other components;
3. `MergeInfo::absorbed_abs`, so the caller reads the absorbed class's value
   after a merge and writes the combined value;
4. invariant W8 in `eg_model_wf`, preserved by every operation;
5. the archive extension, so `restore` returns every handle and every pool
   entry to its state at the matching mark.

The class layer does not compute abstract values, meets or reductions. The
saturation engine in `egraph` computes the meet on a merge and calls this API;
the domain registry in `abstract-domains` defines the fixed-width entry
format. This crate must not depend on `abstract-domains`.

## 2. API

All signatures in this section are proposals.

### 2.1 Entry type

The pool stores entries of a type parameter `A: Copy + Default`. The class
layer never inspects an entry; it stores, copies and restores it. The width of
`A` is fixed by `abs-domain-registry`. A default `A = NoAbs`, a zero-sized
unit type, keeps existing instantiations source-compatible.

```rust
// EClasses gains the entry type after the store policy.
pub struct EClasses<T, K, L, N, J, const TRACK: bool, const PROOFS: bool,
                    P = HotFirst, A = NoAbs>
where
    // existing bounds, plus:
    P: PlainFamily<A, usize, TRACK>,
    A: Copy + Default;
```

### 2.2 Class payload and merge result

```rust
pub struct ClassData<L: DenseId, T: DenseId> {
    // existing fields: use_list, min_row, atomic, matchable, size
    pub abs: Option<<T as DenseId>::Index>,
}

pub struct MergeInfo<T: DenseId, L: DenseId> {
    // existing fields: survivor, absorbed, absorbed_uses, absorbed_min_row,
    // absorbed_atomic
    pub absorbed_abs: Option<<T as DenseId>::Index>,
}
```

`add_singleton` sets `abs: None`. `merge` copies the absorbed class's handle
into `absorbed_abs` and leaves the survivor's handle and the pool unchanged.
The absorbed entry stays allocated until a restore truncates the pool, so the
caller reads it through `abs_value_at`.

### 2.3 Field and spec views

```rust
// field, next to min_pool
pub(crate) abs_pool: SpVec<A, usize, <P as PlainFamily<A, usize, TRACK>>::Store, TRACK>,

// spec views, next to pool_view / pool_archive
pub open(crate) spec fn abs_pool_view(&self) -> Seq<A>;
pub open(crate) spec fn abs_pool_archive(&self) -> Seq<Seq<A>>;
/// The value of live class `id`: None without a handle, else the pool entry.
pub open(crate) spec fn abs_value_spec(&self, id: nat) -> Option<A>;
```

### 2.4 Operations

```rust
pub fn abs_handle(&self, key: K) -> (h: Option<<T as DenseId>::Index>)
    requires self.wf(),
    ensures h == self.class_data_spec(key.as_nat()).abs;

pub fn abs_value(&self, key: K) -> (r: Option<A>)
    requires self.wf(),
    ensures r == self.abs_value_spec(key.as_nat());

/// Reads the entry a MergeInfo handle names (the min_monomial_at_row shape).
/// Refuses an unallocated handle.
pub fn abs_value_at(&self, h: Option<<T as DenseId>::Index>) -> (r: Option<A>)
    requires self.wf(),
    ensures h matches Some(i) ==> r == Some(self.abs_pool_view()[i.as_nat() as int]),
            h is None ==> r is None;

/// Allocates the class's entry on first use, else overwrites it.
/// Both paths are tracked writes. Refuses a dead key or pool exhaustion.
pub fn set_abs_value(&mut self, key: K, v: A)
    requires old(self).wf(),
    ensures
        final(self).wf(),
        final(self).n_spec() == old(self).n_spec(),
        final(self).roots_view() == old(self).roots_view(),
        final(self).num_classes_spec() == old(self).num_classes_spec(),
        final(self).min_width_spec() == old(self).min_width_spec(),
        final(self).abs_value_spec(key.as_nat()) == Some(v),
        forall|id: nat| id != key.as_nat() && old(self).reprs.contains_spec(id)
            ==> final(self).abs_value_spec(id) == old(self).abs_value_spec(id);
```

`merge_with` gains two ensures, carried to `merge`, `merge_directed`,
`merge_directed_with` and the `merge_justified*` forms:

```rust
// inside the `r matches Some(mi)` block of merge_with
&&& mi.absorbed_abs == old(self).class_data_spec(
        old(self).key_of(mi.absorbed.id_nat() as int)).abs
&&& final(self).abs_pool_view() == old(self).abs_pool_view()
```

The second clause gives the caller `abs_value_at(mi.absorbed_abs)` with the
pre-merge entry. The caller then calls `set_abs_value(survivor_key, meet)`.

## 3. Invariant W8

W8 joins the W-invariant table in the `eclasses.rs` module header, in the
style of W6:

> W8: the abstract-value pool is whole entries; live handles are allocated and
> pairwise distinct.

Stated over the views of `eg_model_wf`, with `abs_pool: Seq<A>` a new
parameter:

```rust
// W8a: whole entries. One cell holds one entry of type A, so the pool
// length counts entries and no write splits an entry.
// W8b: live handles are allocated
&&& (forall|id: nat| #[trigger] ss_contains(reprs_sparse, reprs_indices, live, id)
        && ss_value(reprs_dense, reprs_sparse, id).abs is Some
        ==> ss_value(reprs_dense, reprs_sparse, id).abs->Some_0.as_nat()
            < abs_pool.len())
// W8c: live handles are pairwise distinct
&&& (forall|id1: nat, id2: nat|
        ss_contains(reprs_sparse, reprs_indices, live, id1)
            && ss_contains(reprs_sparse, reprs_indices, live, id2) && id1 != id2
            && #[trigger] ss_value(reprs_dense, reprs_sparse, id1).abs is Some
            && #[trigger] ss_value(reprs_dense, reprs_sparse, id2).abs is Some
            ==> ss_value(reprs_dense, reprs_sparse, id1).abs->Some_0.as_nat()
                != ss_value(reprs_dense, reprs_sparse, id2).abs->Some_0.as_nat())
```

An entry stored across `abs_width > 1` cells, which §7 rejects, would make W8a
`abs_width > 0 ==> abs_pool.len() % abs_width == 0`. W8b then becomes
`(h + 1) * abs_width <= abs_pool.len()`, the exact shape of W6. If `A` carries
a decode predicate, W8a also states it per cell, as the pool-cells-decode
clause does for `Opt<T>`.

W8c is the frame condition of `set_abs_value`: writing one class's entry
leaves every other live class's value unchanged.

Per operation, the proof obligation is:

| Operation | Handles | Pool | W8 argument |
|---|---|---|---|
| `new` | none live | empty | vacuous |
| `add_singleton` | new key gets `None` | unchanged | old handles keep W8 |
| `merge_with` | absorbed key removed, survivor unchanged | unchanged | a subset of the old live handles |
| `set_abs_value`, first write | key gets `len` | grows by 1 | `len` exceeds every old handle, so it is fresh |
| `set_abs_value`, overwrite | unchanged | 1 cell written | handles and length unchanged |
| `set_min_monomial`, `set_atomic`, `set_class_matchable`, `add_use`, `splice_uses` | `abs` carried | unchanged | old W8 |
| `restore_frames`, `reset_frames` | archived | archived | per-frame W8 from the archive |

`merge_with` discharges W8 in `lemma_merge_wf`. The survivor's payload write
there must carry `abs` unchanged, as it carries `min_row`.

## 4. Archive and restore obligation

The handle lives in `ClassData`, so the repr set's dense column already
restores it. The pool is a new component with its own frame stack. The
obligation is that both restore together.

1. `eg_archive_agrees` gains a parameter `abs_snaps: Seq<Seq<A>>` with three
   clauses: `abs_snaps.len() == f`; `eg_model_wf` holds per frame `k` with
   `abs_snaps[k]`, so W8 holds in every archived mark; and archived lengths
   are monotone, `abs_snaps[k1].len() <= abs_snaps[k2].len()` for
   `k1 <= k2`.
2. `EClasses::wf` gains `abs_pool.wf()` and the bound
   `abs_pool.snapshots_view()[k].len() <= abs_pool.view().len()` for every
   frame, outside the opaque predicate, as for `min_pool`.
3. `push_frames` pushes the pool in lockstep and ensures
   `abs_pool_archive() == old.abs_pool_archive().push(old.abs_pool_view())`.
4. `restore_frames` and `reset_frames` restore the pool in lockstep and ensure
   `abs_pool_view() == old.abs_pool_archive()[target]`, with the archive
   truncated as for `pool_archive`.
5. The component depth checks in the three frame functions include
   `abs_pool.depth_exec()`.
6. The `Member` impl in `group.rs` adds the pool view to `Model` and `archive`.

Together with the existing `reprs_dense_view() == old.reprs_dense_archive()[f]`,
items 3 and 4 give the semi-persistence theorem for abstract values. For every
class key live at mark `f`, after a restore to `f`, the class's handle and its
pool entry equal their values at mark `f`. `restore_frames` and
`reset_frames` state this theorem as an ensures in terms of `abs_value_spec`.

## 5. Payload size

`egraph/src/classes.rs` pins the `ClassData` repr at 16 bytes for 31-bit ids
and at most 32 bytes for 63-bit ids. The current repr holds three index words
(use list, `min_row`, `size`) and three flags (`present`, `atomic`,
`matchable`): 15 bytes, padded to 16 at 31-bit ids, and 27 bytes, padded to
32 at 63-bit ids. A separate `(handle, present)` pair adds one word and one
byte, so the assert fails at both widths. This is the first design decision.

| Option | 31-bit repr | 63-bit repr | Cost | Proof work |
|---|---|---|---|---|
| A. Widen the budget: store `abs` as `(handle, present)`, as `min_row` is stored | 20 bytes (+25%) | 40 bytes (+25%) | 4 bytes per class at 31-bit ids, in the live column and in every captured old value | the `min_row` pattern; no new technique |
| B1. Share a word: one side-row number indexes both the `min_pool` row and the pool entry | 16 bytes | 32 bytes | a class with only one of the two allocates both; the two pools grow in lockstep | W6 and W8 share one allocation clause; `set_min_monomial` and `set_abs_value` share allocation |
| B2. Share bits: encode `None` as a sentinel index and move the flags into spare high bits of the index words | 16 bytes | 32 bytes | decode costs a mask per read | new `repr_wf` and extensionality proofs for packed words; the use-list word's high bit already carries the capture tag |

Option A was chosen (§7) and measured against main at `16cd7599` on the
corpus programs. Peak RSS changes by at most +4.1% at 31-bit ids and +8.6%
at 63-bit ids (math-microbenchmark), under 0.2% on the largest program
(acgen), and wall time stays within run-to-run spread. Both asserts in
`egraph/src/classes.rs` carry the full numbers.

A further option drops the handle and indexes the pool by class key. The key
is unique per live class and survives a merge as the survivor's key. This
option keeps 16 bytes and makes W8c hold by construction. It departs from the
handle design of eclass-analysis.md §4 and sizes the pool by the key range,
and it was not chosen.

## 6. Where the change lives

- `containers-verus/src/eclasses.rs`: `ClassData::abs` and its repr,
  `EqSpec::eq_exec`, W8 in `eg_model_wf`, the pool snapshots in
  `eg_archive_agrees`, the `abs_pool` field, `MergeInfo::absorbed_abs`,
  `set_abs_value`, `abs_handle`, `abs_value`, `abs_value_at`, and the pool in
  `push_frames`, `reset_frames` and `restore_frames`.
- `containers-verus/src/group.rs`: the pool in the `Member` model and archive.
- `egraph/src/classes.rs`: the two `ClassData` size asserts.

Every step follows the `min_row` / `min_pool` code: the `(row, present)`
repr pinned by `repr_wf`, W6 for allocation and distinctness, the
`pool_snaps` clauses of `eg_archive_agrees`, first-use allocation in
`set_min_monomial`, and the read through a carried handle in
`min_monomial_at_row`.

The meet on merge belongs to the saturation engine. The unverified reference
`containers/src/eclasses.rs` is a differential oracle and needs no change.

## 7. Design decisions

1. Payload size: option A. `abs` is stored as a `(handle, present)` pair,
   exactly as `min_row` is stored, and `repr_wf` pins the absent value to
   `(min, false)`. The repr grows to 20 bytes at 31-bit ids and 40 bytes at
   63-bit ids. Option A reuses the `min_row` proofs unchanged in shape. B1
   couples the abstract-value pool to `min_pool`, so a class with only one of
   the two allocates both, and `set_min_monomial` and `set_abs_value` share
   one allocation proof. B2 needs new `repr_wf` and extensionality proofs for
   packed words, and the use-list word's high bit already carries the capture
   tag. The peak-memory and wall-time measurement is recorded in the size
   assert comments in `egraph/src/classes.rs`.
2. Entry representation: a type parameter `A: Copy + Default`, default
   `NoAbs`. One entry is one pool cell, so W8a holds by the cell type and no
   `abs_width` arithmetic enters W8b. The entry format stays the business of
   `abs-domain-registry`, which instantiates `A`.
3. One pool. The handle stays one index word, which option A sizes. A
   per-sort pool widens the handle to a `(sort tag, offset)` pair and enlarges
   the repr again; it can follow once the registry defines the sorts.
4. No handle adoption. `merge_with` leaves the survivor's payload `abs`
   unchanged, so W8 for the merged state is a subset of the old live handles
   and `merge_with` writes no extra payload. A survivor without a handle gets
   one on its first `set_abs_value`, which costs one pool entry. The test
   `restore_after_merge_with_handle_adoption` is deleted.
5. `set_abs_value` returns nothing. A caller that needs the old value reads
   it with `abs_value` first; the saturation engine reads both inputs of the
   meet before it writes, so it has the old value already.

### Departures from the API of §2

- `abs_value_spec` is defined through the free function
  `abs_value_of(dense, sparse, abs_pool, id)`, so the restore theorem can
  name a value in an archived frame. The meaning is the one in §2.3.
- The restore theorem is an ensures of both `reset_frames` and
  `restore_frames`, and holds for every key, not only the keys live at the
  mark: the restored repr columns and pool are the archived ones.
- The live-length bound on archived pool snapshots sits in `EClasses::wf`,
  outside the opaque `eg_archive_agrees`, as for `min_pool`; the per-frame
  count and the monotone lengths sit inside it, as §4 states.

## 8. Links

- [eclass-analysis.md §4 Storage](../../../egraph/doc/future/eclass-analysis.md#4-storage):
  the storage design this chapter implements.
- [E-Graph Class-Layer Integration](egraph-class-layer.md): the class layer's
  surface and invariants.
- [Chapter 2, The Trust Boundary](02-trust-boundary.md): the
  `external_body` ledger.
- [Chapter 18, Store Policy](18-store-policy.md): the `PlainFamily` column
  family the pool uses.

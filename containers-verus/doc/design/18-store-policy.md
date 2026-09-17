# Store Policy for the Composite Containers

Every tracked column of a composite container (`UnionFind`'s forest,
`SparseSet`'s index columns, the list and ring arenas, the B+ tree's node
arena, the e-class table) is a semi-persistent `Vec` over some `DiffStore`.
Which store fits is a property of the workload, not of the composite, so the
choice is a type parameter of the composite: `P`, defaulting to `HotFirst`.

## 1. Why a policy rather than a store parameter

`Vec<T, I, S, TRACK, VC>` already takes its store `S`. A composite with
several columns of different element types would need one store parameter per
column, and every consumer would have to spell all of them. The policy is one
parameter that answers "which store for a column of this element type", so a
consumer names one type and every column follows.

The answer depends on the element type: `InlineStore` steals its capture bit
from a spare bit of the element's repr and therefore needs `T: Tagged`;
`ParallelStore` keeps a side flag vector and takes any `Copy` element;
`TrailStore` takes any `Copy` element. Plain traits cannot branch on "is `T`
tagged" (that is specialization), so the policy is consulted through two
families, chosen by the column rather than by the policy:

```rust
pub trait TaggedFamily<T: Tagged, I: IndexLike, const TRACK: bool> {
    type Store: DiffStore<T, I, TRACK>;
    fn empty() -> (s: Self::Store) ensures s.wf(), s.data().len() == 0;
}
pub trait PlainFamily<T: Sized + Copy, I: IndexLike, const TRACK: bool> { /* same shape */ }
```

A composite declares, for each column, the family that fits the column's
element type, and builds the column through `Vec::with_store(P::empty())`.
No generic associated types are involved; the projection
`<P as TaggedFamily<T, I, TRACK>>::Store` is an ordinary associated type.

## 2. The two policies

| Policy       | Tagged column  | Plain column    | Fits                                        |
|--------------|----------------|-----------------|---------------------------------------------|
| `HotFirst`   | `InlineStore`  | `ParallelStore` | many writes per frame (equality saturation) |
| `TrailFirst` | `TrailStore`   | `TrailStore`    | many marks and restores, few writes (SMT)   |

`HotFirst` reproduces the stores the composites hardcoded before the policy
existed, so nothing observable changes under the default. The difference
between the two is the ingress discipline: the Hot-first stores dedupe on
first capture (one saved word per touched slot per frame, a lookup per
write), the Trail store appends every write (no lookup, duplicates retained
until rollover). Equality saturation iterates rewrite rounds to a fixpoint
between marks, so its columns are written many times per frame and dedupe
pays; SMT-style search marks and backtracks constantly with few writes per
frame, so the append-only ingress pays.

## 3. What the abstract store changed in the proofs

The composites' proofs were already stated over the `Vec` contract, so
abstracting the store changed no proof argument. Two facts that the concrete
`InlineStore` had been supplying through its open `wf` had to be stated once
for every store:

- The frame-pushing `Vec` entry points (`push_frame`, `seal_frame`) require
  the column's length to fit its index word. `DiffStore` gained the universal
  lemma `lemma_wf_data_len` (`wf ==> data().len() < I::max_nat()`), which each
  of the four stores discharges from its own `wf`; composites call it before
  pushing a frame and inside the arena's row-fits lemmas.
- The arenas' total-operation guards read the store's `data` field for its
  length; they now use the trait's `raw_len()`.

## 4. Where the parameter reaches

`UnionFind<T, J, TRACK, PROOFS, P>` (parent, rank, and the two proof
columns are tagged families); `SparseSet<T, Idx, S, TRACK, VC, P>` (the two
index columns; `dense` keeps its explicit `S`); `CircularList<T, N, TRACK, P>`
and its `RingIter`; `ListArena<T, L, N, TRACK, P>` and its `ListIter`;
`BPlusTreeSet<K, L, S, TRACK, P>` and its `BPlusCursor`; and
`EClasses<T, K, L, N, J, TRACK, PROOFS, P>`, which threads `P` into its four
composites and gives its min-monomial pool (an `Opt<T>` column, which owns
its niche bit and cannot be tagged) the plain family. Consumers that name
these types with the old argument lists compile unchanged.

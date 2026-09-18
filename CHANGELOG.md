# Changelog

## [Unreleased]

### Changed

- Version tokens now carry their minting manager, a generation and a depth
  (`GroupToken`; `VecToken` is an alias); every container is a group of one
  with its own token manager, and a token from another container is refused.
- `restore(t)` resets to the checkpoint and keeps its frame open (semantics
  B): the token stays valid and can be restored to again, every token minted
  after it is dead, and the new `pop_scope` / `try_pop_scope` (with
  `ContainerError::NoOpenFrame`) drops the open top frame. The SMT-LIB
  `pop` is `restore_and_pop(t)` / `try_restore_and_pop(t)`: the two fused
  on one pop core, at the legacy restore's cost. The e-graph gains
  `EGraph::pop_scope` and `EGraph::restore_and_pop`; its interpreter's
  `(pop)` is the fused call. The stamp table
  behind token validity is O(1) per mark and per restore, and a restore
  never migrates tier history (the reopened frame is a header push with a
  deferred rollover; the next `mark` applies the tier policy once).
- The e-graph literal store is a verified `SpMap` keyed by canonical keys
  (`LitVal::Key`, `CanonicalKey`): floats intern under `CanonicalF64`,
  rationals under `CanonicalRational`.
- Byte reporters (`heap_bytes`, `tracking_bytes`, `total_bytes`,
  `diff_log_len`) are plain Rust outside the verified perimeter; the
  `HeapBytes` trait is exported for stores, and `DiffStore` no longer has a
  `heap_bytes` method.
- The Trail dedupe takes a verified straight-copy fast path on strictly
  ascending frames.

- The fork-history manager is always provided from the outside:
  `group::ForkHistory<M: Member>` owns one `History` and one typed member.
  Members carry no tokens — their versioning surface is structural
  (`push_frame`, `reset_frame`, `restore_frame`, `pop_frame`, `depth_exec`) —
  and the group answers `mark` (`Option<GroupToken>`),
  `restore`/`restore_and_pop`/`pop_scope` (`bool`), `mint_pushed`, `is_valid`,
  `depth` and `in_lockstep`. Every container in the crate is a `Member`,
  `Pair<A, B>` forwards to two members and nests, and a standalone container
  is a group of one (`ForkHistory::new(Vec::new())`). `Deref`/`DerefMut` keep
  typed access. A member driven behind the group's back drifts and the next
  group operation refuses, changing nothing.
- The e-graph runs its nine synchronized members on one `History` through a
  borrowed forwarding view (`EGraphMembers`): no per-member token stacks, one
  token per scope for the whole e-graph. Store traces land at 0.97–1.00× of
  the previous commit, `empty20k` at 0.79–0.80×, saturation at parity.

### Removed

- Every container's own versioning surface. `Vec`, `AppendOnlyVec`, `SpMap`,
  `SparseSet`, `CircularList`, `ListArena`, `UnionFind`, `BPlusTreeSet`,
  `EClasses` and `HintedArena` no longer have `mark`, `try_mark`, `restore`,
  `try_restore`, `restore_and_pop`, `try_restore_and_pop`, `pop_scope`,
  `try_pop_scope` or `is_valid_token`, and the token types (`MapToken`,
  `SparseSetToken`, `CircularListToken`, `ListArenaToken`, `UnionFindToken`,
  `BPlusToken`, `EClassesToken`) are gone; `VecToken` remains as the alias for
  the group's `GroupToken`. Version a container by putting it in a
  `ForkHistory` group of one. `Vec` and `AppendOnlyVec` also lost the embedded
  `Genealogy`: the branch cut happens in the group's `History`.
- The predecessor dyn group (`sync_group`, with `Box<dyn SyncMember>`
  members) and the `Solo`/`SyncPair` migration wrappers.
- In the e-graph, the wrappers' token layer: `CacheToken`, `PoolCacheToken`,
  `NodeStoreToken`, `RoutingToken`, `LitValStoreToken` and the registry
  tokens. The director pool takes the frame protocol instead.

### Added

- Randomized grouped-history tests at the `ForkHistory` and e-graph levels,
  and a typed-group suite (`tests/typed_group.rs`): a group of one per
  container, a nested `Pair` of three columns under one history driven by a
  randomized lockstep proptest, and the refusal cases.

## [0.3.0] - 2026-08-28

### Added

- Added the Semper book, with executable examples covering the language,
  algebraic canonization, saturation, anti-unification, and policy repair.

### Changed

- Made malformed algebraic declarations and rule right-hand sides fail during
  resolution instead of relying on unchecked representation invariants.
- Clarified that anti-unification optimality is relative to the equalities
  materialized in the selected e-graph completion mode.
- Aligned every workspace package and internal published dependency at
  version `0.3.0`.

### Fixed

- Honored `:assoc-left` and `:assoc-right` flattening directions during both
  source-term construction and rewrite right-hand-side construction.
- Rejected algebraic operators whose argument and result sorts make variadic
  singleton collapse unsound, as well as conflicting associativity tags.
- Added lexically scoped right-hand-side comprehension locals without mutating
  query match shapes or runtime match rows.
- Enforced collection element sorts, fixed right-hand-side arity, and
  literal-producing comprehension filters.
- Rebuilt before every `run :until` observation, including the final
  observation after exhausting the rule-round budget.

## [0.2.0] - 2026-08-25

### Added

- Published `semi-persistent-containers-verus`, the executable
  Verus-verified container layer used by the e-graph.
- Added canonical license, conduct, contribution, and security documents to
  every workspace package, with a CI gate for package metadata and source
  headers.
- Added Exact and Monte Carlo graph search for e-graph anti-unification,
  including explicit cycle policies and rewrite-aware semantic diffing.
- Added native associative, commutative, and idempotent canonization across
  construction, matching, and anti-unification.
- Added plain, eager, and goal-directed lazy AC congruence-closure modes.
- Added deterministic batch proof-path export using an Euler-tour LCA index.

### Changed

- Switched `semi-persistent-egraph` to the verified container implementation;
  the independent Rust implementation remains available as a differential and
  performance reference.
- Reworked AC matching around maximum partitions so its exponential factor is
  in pattern variables and distinct children rather than child multiplicity.
- Made pool-backed variadic recursion-scheme nodes traversable and deduplicated
  by their child sequences.
- Aligned every workspace package and internal published dependency at
  version `0.2.0`.

### Verification

- Added differential, property, layout, and regression coverage between the
  verified and reference container implementations.
- Added Verus proofs for the container protocol and selected
  anti-unification objective and lower-bound lemmas. The exact scope and
  remaining obligations are maintained in [`doc/claims.md`](doc/claims.md).

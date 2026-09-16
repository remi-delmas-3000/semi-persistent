# Conditional interface review and existing-proof classification

## Evidence and scope

The complete conditional operation family, legal public-operation traces, and
arbitrary legal rollover traces verify in `composition.rs`: **79 verified,
0 errors** with pinned Verus `0.2026.08.02.b677dd5`. There are no imported leaf
implementations or trusted proof stubs. The mathematical witness implements all
provisional method contracts; additional encoded examples exercise duplicates,
sorting, gapped runs, preserved pool prefixes, and empty frames.

This completes the first **conditional composition** milestone. It does not
complete the thread goal or discharge any missing production implementation.
The interface predicates below remain concrete-adapter obligations. Their
definitions may be strengthened or decomposed as implementation evidence
requires; every interface revision must reverify the complete composition.

Production verification at `07b6df8` remains separate evidence: both configurations
verified 2310 obligations; feature, differential and consumer gates passed.
No production source was changed during the conditional milestone.

## Requirement audit

| Requirement | Conditional evidence |
|---|---|
| One saved length and earliest-capture map per frame | `model::Frame`, `frame_ok`; `encoding::earliest`, `trail_append_equation`, `repeated_capture` |
| Constructor, writes, push/pop, regrowth, mark, restore | `model` closure lemmas and `mutation`/`policy`/`composition` public wrappers |
| All legal public-operation interleavings | `public_sequence::execute_one`, `effect_preserves`, `complete_sequence` |
| Any legal rollover order, independent of selector | `policy::legal_rollover_sequence`; `apply_policy_sequence`; Hot-then-Trail witness |
| Batched pair replay and direct Cold replay | `composition::reconstruct`, `cold_suffix`; `model::range_split` |
| Arbitrary saved-length zigzags and arbitrary resize filler | `model::range_reconstructs`, `reconstructs_target`; witness lengths 3,1,3,2,2 |
| Precise logical and canonical retirement | `Runtime::retire`, `restore_public`; required exact physical prefix projection |
| Every survivor tier and both disciplines | Separate `reopen_hot`/`reopen_cold` interfaces and dispatch; `mixed_restore_cases` |
| Capture rebuilding and fused/non-fused protocols | `prepare`, `pair_batch`, `finish_capture`; witnesses parameterized over clearing protocol |
| Mutation followed by another older restore | `restore_write_restore`, `mutate_then_restore_older`; definite successful witness |
| Empty frames, duplicate captures, local transforms | `empty_frame_migration`, `empty_frame_contracts`, `encoded_duplicate_example`, `conversion_chain` |
| Exact pool append followed by frame publication | `appended`, `appended_cold`, `appended_cold_meaning`, `cold_transform_and_pool` |
| Completed prefix relocation preserves frame order | `move_prefix_preserves`; completed migration count/map contracts |
| Public tokens and rejected requests | Separate token predicate and bounds interface; typed errors and exact unchanged-state rejection effects |
| No extra runtime history or changed replay batching | Isolated proof target; all traces/maps are mathematical parameters or derived views |

## Boundary review against current source

### Canonical history

`Vec::wf_for_snap` combines store/partition facts, canonical boundary shape and
canonical frame reconstruction. The whole predicate cannot serve as
`canonical_ok` during resize/replay: changing live contents temporarily breaks
the newest canonical frame's layer relation.

The adapter must separate canonical boundary/storage correspondence from
`SnapshotsOK`. It must recover **all** of `wf_for_snap` at public boundaries,
including the old `full_trail` frame contracts. This is not permission to drop
canonical contracts or use the inert `diff_log` as replay authority.

Current physical and canonical invariants each reconstruct snapshots, but this
alone does not prove equality of their capture domains. If the adapter uses
canonical-to-physical map equality, that relationship needs its own proof or
stronger preserved invariant. It cannot be inferred from equal reconstructed
contents. The physical map remains the shared reconstruction authority.

`Vec::restored_history_prefix` already specifies exact retained headers, runs,
payloads, snapshot boundaries and chronological ghost prefix. It is the candidate
for `retired_prefix`. `hot_survivor_promoted` specifies the subsequent movement
separately, which is correct: exact pre-state physical-prefix equality is not
required after moving the survivor.

### DiffStore implementation connection

The writable tier comes from the `DiffStore` implementation's immutable capture
discipline. `Vec` consults it for capture, mark, and survivor reopening. The
rollover selector is a separate configuration input; its eligibility proof must
respect that writable tier and protect the active frame.

| Implementation | Writable tier | Reads replay indices for pre-clear | Replay clears named capture flags |
|---|---|---|---|
| `TrailStore` | Trail | No | No (capture flags are ghost state) |
| `ParallelStore` | Hot | No (bitmap reset) | No |
| `InlineStore` | Hot | Yes (sparse tag reset) | Yes |
| `DynStore` | Selected variant's tier | Selected variant's protocol | Selected variant's protocol |

`DiffStore` mutation contracts preserve all three protocol predicates. This is
essential for `DynStore`: the proofs use an instance property that remains
constant across operations, not a hard-coded generic type test.

The concrete dependency chain is:

- `capture` supplies the store-level append/no-op contract. The checked Hot
  path consumes it; the current trusted Trail fallback instead appends directly
  after `get`. Its concrete proof must establish the same `capture_first` map
  effect, retaining physical duplicates and updating the existing ghost capture
  view consistently. A trait contract cannot be credited to a bypassing caller.
- `set_raw`, `push`, and `pop` supply exact live effects and flag framing.
  `Vec` must preserve older maps and handle active-domain capture/regrowth.
- `prepare_mark` clears capture state under its coverage premise. `Vec` seals
  and opens the tier selected by the store, then applies legal rollover.
- `resize_default`, `begin_restore`, `restore_overlay`, and `restore_run`
  supply resize, clearing, batched pair replay, and direct Cold replay effects.
  The checked shared-map replay bridge consumes these existing contracts.
- `finish_restore` supplies capture membership for the reopened frame's entries.
  The checked finalization and map-membership bridges connect it to `CaptureOK`.

These methods have checked implementations in the four store modules and are
included in full production verification. Capacity diagnostics/reclamation have
separate recorded trust boundaries; this is not a claim that every store module
is trust-free. Nor does checking these methods discharge the remaining all-tier
`Vec` mutation, conversion, policy, and Cold reopening composition obligations.

In particular, `runtime_set_fallback` and `runtime_capture` currently call
Hot-only checked helpers under the weaker runtime test `unique_capture()`.
Those helpers require `hot_defer_wf`, which is not supplied merely by a Hot
writable tier with older Cold history. Their enclosing trusted bodies hide
that composition obligation. Reuse the helpers' local arguments while proving
general all-tier framing; do not claim the fallback is checked or strengthen
its public preconditions to the Hot-only case.

### Public guards and payload capabilities

The standalone Vec token predicate is `TRACK && frame_idx < depth && depth <
u32::MAX`. Keep it intact. Group genealogy belongs to the group/history layer;
do not add it to the standalone token or replace public validity with only a
frame-coordinate bound.

Mark checks Untracked, then DepthLimit, then CapacityExhausted. The adapter's
`mark_error` projection and `mark_guard` proof must retain that ordering.
`try_push` rejects with CapacityExhausted; `try_restore` rejects with InvalidToken.
The conditional wrappers retain those result categories and leave the full
state unchanged when rejected.

Mark's existing contract promises the returned coordinate, not unconditional
future token validity. In particular its depth guard and restore's depth guard
must not silently be treated as the same post-mark assertion. The conditional
theorem preserves the existing distinction.

Mutation and marking interfaces do not inherit restoration capability. Concrete
restore requires `T: Default`, whereas the mutation family supports its broader
Copy payload domain. Concrete index limits, tracking/depth guards and settings
framing must be instantiated from existing fields/contracts, not weakened to
match the mathematical witness's unbounded finite-sequence capacity.

### Assumption inventory boundaries

The `README.md` inventory names every provisional method, concrete candidate,
caller premise and next consumer. Local transform relations in `encoding.rs`
name full map equality and validity; completed migration additionally requires
source retirement/rebasing and stable physical ownership. The local pool-builder
contract deliberately does not assert global partition validity while source
and destination coexist.

The consistency witness interprets physical storage directly as frame maps and
canonical storage as snapshot sequences. That interpretation demonstrates that
the contracts are jointly realizable; **it is not the production interpretation**.
The production projections must include the actual pooled storage and canonical
chronological history described above. Opaque predicates must not be defined as
vacuous truths merely to instantiate the interface.

## Existing-proof classification

“Reuse” means retain the checked theorem/body and add the required interpretation
bridge. It does not mean its production adapter is already verified. “Adapt”
means keep existing work while strengthening exported facts or separating a
physical effect from snapshot-specific premises. No verified proof is currently
scheduled for deletion or replacement solely because a new model exists.

| Existing work | Classification | Required work against the conditional contract |
|---|---|---|
| `frame_saved_value`, `lemma_frame_saved_value_contract`, `lemma_physical_frame_step` | Reuse | Derive the finite map and its bounded domain from physical tiers; connect Option lookup to map membership/value |
| `replay_physical_range` | Reuse | Its exact overlay/lookup result already describes arbitrary-buffer application; add map interpretation and batch-composition bridge |
| `replay_cold_range` | Reuse | Exact covered/uncovered per-cell effect and unchanged flags match direct replay; add Cold-map interpretation |
| `replay_pair_suffix_checked`, `replay_cold_frame_checked` | Adapt | Existing wrappers require layer agreement and export snapshot-prefix reconstruction; expose the underlying arbitrary-buffer map effect without discarding reconstruction lemmas |
| `reconstruct_target_checked`, mixed-tier replay orchestrator | Reuse/adapt boundary | Preserve batching and local frozen state; export exact history/protocol framing required by the adapter |
| `restored_history_prefix`, truncation bounds and canonical/physical retention lemmas | Reuse | Translate exact physical prefixes to retained shared-map sequence and instantiate canonical prefix projection |
| `promote_hot_survivor_checked`, `hot_survivor_promoted` | Reuse | Exact rebased payload equality supplies map/domain equality and older-storage framing |
| `finish_survivor_checked`, zero finish, capture rebuilding | Reuse | Relate current captured-in-range predicates to shared-map membership; retain active length and no-stray-flag obligations |
| Capacity-only reclamation proofs | Reuse | Instantiate unchanged relevant sequences, protocol and canonical projection |
| `cold_encode::append_sorted`, `append_cold_sorted_checked` | Adapt | Existing run/input mapping and prefix contracts are useful; expose complete map equality, including absence and source coverage, in the local/pool interface |
| Hot-only capture/set/push/pop/mark proofs | Reuse for their scope; adapt for general case | Retain their checked scope; derive shared-map effects and all-tier preservation rather than claiming Hot-only preconditions cover mixed histories |
| Trusted all-tier mutation/mark fallbacks | Unproved implementation to discharge | Prove actual execution against capture/raw mutation/open-frame contracts; do not transfer trust into new wrappers |
| Trusted Trail dedup/sort/migrations and configured/adaptive execution | Unproved implementation to discharge | Exact local map transforms, pool append, source-plan identity, retirement/rebasing and eligibility; compose through sequence theorem |
| Cold survivor promotion / former restore fallback | Discharged | Checked decoder, exact source prefixes, both destination representations, shared-map equality and finalization compose in `restore_cold_survivor_checked`; obsolete trusted dispatcher removed; full verification and regression gates passed |
| Old specialized Hot-defer reconstruction proofs | Preserve | Useful verified specialization; no need to remove it to establish the all-tier theorem |
| Derived/container and group/parallel paths | Pending concrete public audit | Retain original scope, review content/prefix/error contracts and fan-out trust after Vec adapters are checked |

## Next concrete work

The first concrete bridge now derives `persistence_frame` and
`persistence_model` from actual physical storage and verifies bounded domains,
exact lookup membership/value, snapshot meaning, writable ownership, and the
active capture relation. Pair suffix composition and direct Cold replay export
arbitrary-buffer shared-map application through checked executable helpers.
The original snapshot-oriented wrappers retain their contracts and use those
helpers; their existing reconstruction lemmas remain checked. The shared model
is imported by production, while the provisional interface target stays isolated.

Interpretation, replay, retirement, Hot promotion and capture finalization
bridges are verified milestones. Cold decoding at `25ecbcf` passed full default
and literal-types verification (2360 obligations), feature, differential and
consumer gates. Its local theorem alone did not discharge promotion assembly.

The next step now checks that assembly: exact older Cold prefixes, unchanged
canonical history, store-selected destination header and representation, full
shared-map equality, and capture rebuilding. `restore_cold_survivor_checked`
exports restored contents, depth, snapshot prefix and exact shared-frame prefix.
All 45 selected Cold obligations passed together. The former trusted fallback
and unused trusted survivor dispatcher are discharged/removed, reducing counts
to 79 default plus five literal registrations. Full default and literal-types
verification each passed 2373 obligations; feature, differential and consumer
tests passed. The conditional target remains at 80 verified obligations. An
additional partial-API CI audit reports the same 40 unlisted functions as the
committed baseline; no entries were added by this change or to the allowlist.

1. Complete the production interface instantiation using the checked physical
   interpretation, replay, retirement, promotion and finalization contracts.
2. Discharge remaining capture/mutation/conversion and policy implementations,
   rechecking conditional composition after any interface change.
3. Finish derived/parallel public closure and the full trust/gate audit.

No existing proof is superseded until a concrete replacement verifies. No push
to origin is authorized.

### General canonical capture preservation

`lemma_canonical_capture_append` now proves chronological ghost-history
preservation from `wf_for_snap`, a valid saved-domain capture, unchanged live
contents/snapshots/boundaries, and the caller's new physical partition. It makes
no Hot-only assumption. The proof retains the existing duplicate/first-capture
and unchanged-range lemmas; the original checked Hot canonical-capture helper
now consumes it without changing its executable statements or public contract.
The selected capture family verifies (16 obligations).

The `push_frame` wrapper also verifies directly against the existing
`runtime_push_frame` contract (three selected wrapper/dispatcher obligations).
Its redundant trust marker is removed. The all-tier mark fallback remains
trusted, so this is wrapper discharge rather than complete mark discharge.

The next capture work must establish the general physical pool effect and
capture-membership relation for each store-selected ingress, then compose that
effect with the canonical lemma. The new canonical lemma alone does not prove
the trusted `runtime_capture`, mutation or mark fallbacks.

The regrowth audit also exposes a concrete ghost-state obligation:
`TrailStore::push` appends a clear ghost capture flag, whereas
`runtime_push_fallback` calls `mark_captured` only for unique stores. Regrowth
below the saved length already has a physical capture, so the Trail branch must
restore its ghost membership too before claiming `open_ingress_ok`. The checked
`TrailStore::mark_captured` body is ghost-only; any generic dispatch change must
still be reviewed for runtime/codegen effects. Do not weaken Trail's capture
membership invariant to conceal this missing preservation step.

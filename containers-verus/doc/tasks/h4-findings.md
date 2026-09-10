# H4 findings: parallel mark/restore and the one-history adoption

Closes phase H4 of `h4-f2-f5-correctness-goal.md`, both stages. Every number
names the test that regenerates it.

## H4a: the member fan-out, measured

`EGraph::restore_with` fans the seven member composites out over a
`rayon::scope` on disjoint `&mut` field borrows; the shared bookkeeping
(outcome, worklists, repair watermark) runs strictly after the join. The
differential test (`par_fanout::par_fanout_matches_sequential_and_spawns`)
drives the same grow/mark/restore workload through both paths and asserts
identical observables at every checkpoint: every node's canonical
representative, class count, node count, and re-add probe ids, including
restores past unrestored inner marks. It also asserts the spawn witness: all
seven member closures observed on at least two rayon workers
(`take_fanout_witness`).

Synthetic wall-clock (`par_fanout_bench::par_fanout_wall_clock`, release, 24
rounds per configuration):

| live nodes/frame scale | mark seq -> par | restore seq -> par |
|---|---|---|
| ~12k nodes (256 leaves/round) | 0.10ms -> 2.84ms (**0.03x**) | 3.41ms -> 4.68ms (**0.73x**) |
| ~200k nodes (4096) | 1.33ms -> 4.40ms (**0.30x**) | 116.7ms -> 72.3ms (**1.62x**) |
| ~1.6M nodes (32768) | 7.80ms -> 11.54ms (**0.68x**) | 5205ms -> 4707ms (**1.11x**) |

Decisions taken from the numbers: the public `mark` is always sequential (a
mark is a per-member frame push; the scope dispatch dominates at every
measured size), and the public `restore` gates the fan-out at
`PAR_NODE_MIN = 16384` live nodes with a `SEMPER_PAR` on/off override. The
1.11x at 1.6M nodes against 1.62x at 200k is the member skew: one member
(classes) dominates the restore critical path at large scale, so the
member-level fan-out's ceiling is set by the largest member, not the member
count.

## H4a.5: the corpus profile, and why the corpus wall stays neutral

`SEMPER_PROF` accumulates mark/restore wall in the engine
(`take_markrestore_profile`); the Sundance adapter prints it on teardown. On
the five most backtrack-heavy corpus instances (selected by a full-corpus
sweep of restore time under a 12s cap; CaDiCaL's trajectory is deterministic,
so call counts match across configurations exactly):

| instance | restore (seq) | restore (forced par) | mark | restore share of wall |
|---|---|---|---|---|
| QF_UF_cyclic_scheduler.3 | 919.3ms / 80 calls | 910.9ms (1.01x) | 7.7ms / 2056 calls | 7.7% |
| QF_UF_reader_writer.3 | 745.8ms / 99 | 730.7ms (1.02x) | 14.5ms / 4595 | 6.2% |
| QF_UF_reader_writer.2 | 264.3ms / 68 | 254.3ms (1.04x) | 9.8ms / 4242 | 2.2% |
| QF_UF_cyclic_scheduler.4 | 201.9ms / 40 | 199.2ms (1.01x) | 2.7ms / 745 | 1.7% |
| QF_UF_reader_writer.1 | 133.4ms / 52 | 130.4ms (1.02x) | 4.3ms / 1285 | 1.1% |

The corpus wall is neutral under the fan-out and the profile says why:
restore is at most 7.7% of solve wall even on the most backtrack-heavy
instances (under 1% corpus-wide), mark at most 0.12%, and at corpus graph
sizes the fan-out moves restore only 1.01x to 1.04x. The projected corpus
ceiling is about 3% even if instances reached the 200k-node regime where the
fan-out wins 1.62x. Parallel corpus gains are therefore bounded by Amdahl at
the profile, not by the fan-out implementation; revisit only if a workload is
measured to spend a large fraction of wall in restore at large node counts
(the EqSat regime is the candidate).

## H4b: one History, the token tree collapse, H2

`EGraphToken` is one `GroupToken` plus the completion outcome; the member
token structs moved into depth-indexed stacks inside the e-graph. `restore`
validates the group token once against the e-graph's `History` and records
the branch cut once. **Design decision:** the e-graph pairs its typed members
with a `History` directly instead of moving them into the owning
`ForkHistory` container, because `ForkHistory` owns its members as
`Box<dyn SyncMember>` and the e-graph's hot paths need typed member access;
the genealogy semantics are the same verified `History` in both shapes, and
`Solo`/`SyncPair` are the verified proofs that the pairing composes.

H2 landed with it: `struct Vec` and `struct AppendOnlyVec` carry no `forks`
and no `id` (grep-checked), `VecToken` is a structural `frame_idx` handle,
and branch validity plus forgery rejection live once on the `History`. The
containers' forgery and abandoned-future tests moved to the paired form, and
`structural_vec_restore_is_frame_liveness_only` pins the complementary
semantics of a raw frame handle. Every reconstruction theorem survived
untouched: the genealogy never carried proof weight in `wf`.

## H4b.3: peak fork-history bytes, shared vs duplicated

`sync_group::shared_history_bytes_vs_per_member_duplication` (ten members,
mark to depth, branch cut, re-climb):

| depth | shared History | per-member duplication (10 members) |
|---|---|---|
| 128 | 1,024 B | 10,240 B (10.0x) |
| 1024 | 8,192 B | 81,920 B (10.0x) |
| 4096 | 32,768 B | 327,680 B (10.0x) |

The real e-graph (`par_fanout_bench::shared_fork_history_bytes`): 512 B
shared at depth 64, 8,192 B at depth 1024. The pre-H2 counterfactual is 46
copies (the semi-persistent column census from the member token structure: 9
in EClasses, 29 in the node store, 8 across registries and maps): 23,552 B
and 376,832 B respectively. The duplication factor is exactly the column
count because every column's stamp array grew in lockstep under
`EGraph::mark`.

## Gates at close

`cargo verus verify`: 1964 verified, 0 errors. Containers suite 180 tests,
e-graph suite 1256 tests, 0 failures. Sundance corpus 438 total / 427
correct / 0 incorrect / 11 timeout, identical with and without
`SEMPER_COMPRESS=auto`, unchanged through the collapse and H2.

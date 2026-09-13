# Mainline's container plus a cold stack

The finding that resets the architecture (2026-09-12): the mainline verified
container never had a diff-log type. It carries production's fields verbatim
(`containers-verus/src/vec.rs:647` at `56a06a5`):

    diff_log: std::vec::Vec<(T, I)>,
    frames:   std::vec::Vec<Frame<I>>,

The `DiffLog` enum - `Cols`, the split columns, `Adaptive`, every wrapper -
was introduced by the compression branch itself, and the 5.7x restore
regression plus the residual mark_churn tax were the price of that type, not
of compression. The design is therefore not a redesign: it is mainline's
container unchanged, plus one cold stack beside it.

## Layout (verbatim, the lock target - ruled 2026-09-13)

    struct Vec<T, I, S> {
        store: S,                          // live values Vec<T> + capture discipline

        hot_value_pool: Vec<(T, I)>,       // all uncompressed diffs
        hot_stack: Vec<HotFrame<I>>,       // { saved_len, start, end } into hot_value_pool

        cold_value_pool: Vec<T>,           // all value runs, concatenated
        cold_index_runs: Vec<IndexRun<I>>, // { base, start, len }: run lands at
                                           //   live[base..], values at
                                           //   cold_value_pool[start..start+len]
        cold_stack: Vec<ColdFrame<I>>,     // { runs_start, runs_len, saved_len }
    }

Cold frames are the oldest [0, k), hot frames the most recent [k, n);
depth n = cold_stack.len() + hot_stack.len(). A token's frame_idx resolves
by comparison with the split point; each tier's header carries saved_len.
No unified frame array, no loc tag, no CSR offs column (IndexRun carries
its own len), no dict or plain cold modes in v1 - every cold frame is runs.

## Algorithms (ruled)

- Capture: unique stores check the flag per write; the trail store appends
  unconditionally and its flag hooks are no-ops. Both push into
  hot_value_pool.
- mark(reclaim_policy, compress: bool): push HotFrame{saved_len, start=end
  =pool.len()}; when compress, run the compression pass; reclaim per policy.
- Compression pass (all hot frames migrate, oldest first, IN PLACE in the
  pool slice [start, end) - no stratum materialization):
    1. normalize (a DiffStore hook, called only here so mark(_, false)
       stays O(1) for trail): unique discipline = sort_unstable by index
       (no ties, allocation-free); trail = STABLE sort by index (ties keep
       temporal order), then a forward pass compacting the first entry per
       index group; the frame's effective length shrinks to the kept count.
       Extents never shift: the dead tail is reclaimed when the whole pool
       truncates at the end of the pass.
    2. translate: one traversal of pool[start..start+kept] appending values
       to cold_value_pool, opening an IndexRun at each index discontinuity,
       closing with a ColdFrame. A diffless frame still emits its ColdFrame
       (runs_len 0) - frame count is token identity.
    3. after the last frame: hot_stack clears, hot_value_pool truncates to
       0 always; capacity is released only when reclaim_policy asks.
- Restore cold frame: resize live to saved_len, then per run one clamped
  memcpy cold_value_pool[start..start+len] -> live[base..].
- Restore hot frame: reverse walk of pool[start..end] (high to low), so
  the most ancient value lands last - correct for trail duplicates.
- Pop: hot = pop header + truncate pool to its start; cold = pop header +
  truncate cold_index_runs to runs_start and cold_value_pool to the popped
  frame's first run start.

Known honesty note: Rust's stable slice sort uses a transient merge buffer,
so the trail normalize is pool-in-place but not allocation-free during the
sort; the unique branch is. Upgrade (in-place stable merge, or decoration
into the frame's own dead tail) only when a profile shows it.

## Method (exec-first, per the 2026-09-12 direction)

Make it work, make it fast, then prove it: implement on the bare fields,
validate against the conformance differential suite, benchmark against the
mainline baseline (the write path must sit at +-0 by identity; a new
deep-history benchmark times the cold memcpy restore in isolation), LOCK the
algorithm, then re-attach proofs. During the exec phase changed bodies carry
their intended contracts as external_body scaffolding recorded here; the
locked state discharges them, reusing commit 20's proof assets (ColdStack wf
and restores, the dedupe overlay theorem, the fold frame rule) at the two
seams.

## Phases (ruled 2026-09-13: fuzz and tune BEFORE any proof)

- A2a: delete the DiffLog type; bare `diff_log` field; compression off;
  every gate green; mark_churn == mainline by identity. DONE - measured
  3.898us vs prod 3.843us on mark_churn/1000 (1.4%), restore_replay
  163.6us vs prod 207.8us.
- A2b: the ruled two-stack layout + mark-driven compression + tier-aware
  restore. Gate: full conformance including trail compression. DONE
  pending env_lever cadence update.
- A2c FUZZ: proptest differential fuzzing against the production container
  as oracle - arbitrary op sequences (push/pop/set/mark with and without
  compression/restore/deep restore across the cold boundary), all stores
  (inline/parallel/trail/dyn), duplicate-heavy trail workloads, degenerate
  frames (empty, single-cell, full-width), pop-into-marked-region, high
  iteration counts. No proof work until this suite is green and has run
  long enough to be boring.
- A2d PERF: benchmark battery vs the mainline baseline (mark_churn,
  restore_replay, a new deep-history cold-restore bench, trail-heavy
  churn); tune normalize (sort choice), run translation, and the capacity
  policies until the numbers stop improving. Record every experiment.
- A3 LOCK + PROVE: freeze the algorithm, then discharge the scaffolding
  ledger (restore_frame, compress_all_hot, store hooks, restore loops),
  reusing commit 20's proof assets at the seams.


## Findings during hardening (2026-09-13)

**The orphan-stratum defect (found by proptest, fixed).** After a cold-target
restore clears the hot stack, subsequent writes capture into the pool with no
HotFrame owner: they are the cold top frame's stratum continuing in the pool
(mainline's "top stratum extends to the log end", in two-stack form). The
compression pass walked only hot_stack and truncated the pool, destroying
those undo pairs; a later restore then failed to roll the cell back. Minimal
case: marks past the buffer, restore into cold, one write, marks past the
buffer again. Fix: the pass folds the orphan prefix into the cold top frame
first - normalize, drop cells the frame's sealed (older, first-wins) runs
already cover, append the rest as new runs, bump the header. Replay order was
already correct (pool backward, then cold frames newest-first) because the
orphan sits at the pool's start and its owner is always cold_stack.last().
Regression net: trail_semi_persistence proptests (random ops and deep unwind,
every op differentially checked, 256 cases).

**Normalize sort measurement (partial).** packed-u64-key decoration sort
(index << 32 | position, sort_unstable, group-first walk reading payloads by
position) beats the tuple sorts at every measured size on the unique shape:
76 vs 86 ns at 32, 1.10 vs 1.12 us at 256, 23.9 vs 26.2 us at 4096
(normalize_bench). Margins are modest; the trail-shaped group (where packed
replaces the ~20% slower stable sort + fold) is still to be measured, and
adoption is gated on it. T stays opaque under the packed scheme; 31-bit
IndexLike packs, wide indices keep the comparison path.

## The proof architecture (deliverable 5 of the hardening goal, ruled 2026-09-13)

One ghost model, four abstraction maps. The ghost diff stores everything
explicitly: every tracked write, in temporal order, duplicates included.

    ghost full_trail: Seq<(T, I)>     // (old_value, index) per write, all of them
    ghost trail_frames: Seq<nat>      // stratum start offsets, one per mark

Maintained at the container layer, independent of the store discipline:
set pushes (old_value, i) whenever a frame is live, mark pushes a boundary,
restore truncates both to the target boundary. Restore correctness is stated
ONCE, against the ghost: overlaying stratum k of full_trail (first-entry-
wins, backward application) onto the layer above reconstructs snapshot k.
Every wf clause about reconstruction reads full_trail, never a physical
representation.

Each physical representation then carries an abstraction theorem relating
its bytes to its ghost stratum, and correctness flows through overlay
equivalence:

- T1, trail hot frame: the pool slice IS the ghost stratum - identity.
  Capture appends to both equally; nothing to transport.
- T2, unique-capture hot frame: the pool slice equals
  dedupe_first_spec(ghost stratum) - the capture flag check is an ONLINE
  dedupe (inductive per write: flag set iff the cell already appears in the
  stratum, so the skip keeps exactly the first capture). Overlay-equal by
  lemma_overlay_dedupe_first (proved, commit 20, no hypotheses).
- T3, cold frame: the runs decoding is a sorted unique-index permutation of
  dedupe_first_spec(ghost stratum) - the normalize hook's postcondition plus
  the translation's. Overlay-equal by composing the dedupe lemma with
  order-independence of unique write sets (lemma_apply_all_eq_overlay) and
  the write_block extensionality chain for the memcpy restore (both proved,
  commit 20).
- T4, the orphan extension: the cold top frame's ghost stratum splits as
  sealed-part ++ pool-extension; the fold's covered-cell drop is
  dedupe-first across the concatenation (the sealed entries are the
  chronologically earlier captures, so first-entry-wins keeps them), the
  same lemma family as T2.

Sequencing: ghost model + wf rephrasing first (the hot-path proofs are
mainline-shaped and port); then T1/T2 (small), T3 (the commit-20 assets
attach), T4 (new, one lemma); then the scaffolding ledger discharges
against the ghost-level contracts.


## D3 result (2026-09-13, packed normalize)

mark_churn/verus control-corrected vs prod, same-run (the saved mainline
baseline's machine had drifted; within-run control is the honest metric):
+6.4% (1k), -1.0% (100k), +5.1% (1M, clean re-run) - all within +-8%.
restore_replay/verified 27% faster than its legacy control (232 vs 318 us
on a loaded machine; ratio matches the earlier 142/208 clean read).
Controls move together across runs (machine load), so absolute cross-run
comparison is not used. Packed-key normalize adopted; numbers in the
perf(vec) commit.

## D5 status (in progress): ghost trail not yet maintained by mutators

The layout and specs are ghost-rephrased (full_trail/trail_frames fields,
wf/wf_for_snap/stratum specs over the ghost, bounds+monotone lemmas
ported). REMAINING OBLIGATION before any spec proves: the exec mutators
(push, push_frame, pop, set_index, restore_frame, compress_all_hot) must
update full_trail/trail_frames as ghost writes mirroring the physical ops,
and the ~24 lemma-body references to the removed `frames` field must move
to g_start/g_end/g_saved_len. Then repr_ok's opaque clauses land with
their T1-T4 theorems. This is the deferred proof grind, now the critical
path; exec is unaffected and green.


## ALGORITHM LOCK (D4, 2026-09-13)

The exec algorithm is LOCKED at this commit. The ruled layout and its
lifecycle (mark-driven compression with the packed-key normalize, orphan
fold, tier-aware restore, both capture disciplines through one path) are
final; the proof phase (D5-D7) attaches to this shape and may not change
it except to fix a defect a proof exposes (which would reopen the lock
with a recorded reason). Lock bar met: 27/27 conformance binaries, trail
semi-persistence proptests at 256 cases, 38/38 in-crate tests, D3
benchmarks control-corrected in band. Everything below the lock is proof
work against fixed code.


## D5 crux identified (2026-09-13): repr_ok needs the open-frame clause

State: 2162 obligations verify, 10 functions remain (down from 41 name
errors). The reconstruction lemmas (cell_eq_overlay, bounds, monotone) are
ported to the ghost trail; the frame-count bridge and no-frames-empty
clauses are in wf. The remaining 10 are the mutator wf-preservation proofs
(push/set_index/pop/push_frame) plus the store restore_overlay
preconditions, and they share ONE root cause:

  wf now demands frame_inv_range over full_trail@, but the mutators prove it
  over diff_log@ (the physical log), and repr_ok - which must relate the two
  - is still `true` (no relationship). So a physical write cannot be tied to
  the ghost stratum.

The fix is the T1/T2 abstraction landed as repr_ok's OPEN-FRAME clause: for
the top (open, hot) frame, the physical diff_log slice
[top.start, diff_log.len()) and the ghost open stratum
[g_start(top), full_trail.len()) must relate so frame_inv_range transfers -
identity for the trail discipline, dedupe_first for unique capture, unified
by overlay-equality (lemma_overlay_dedupe_first). This is the load-bearing
design step of D5 (per the goal: 'Vec::wf ... phrased against the ghost' via
the equivalences), not a mechanical edit; it wants careful statement so the
mutators' per-cell obligations discharge from it. NEXT: design the
open-frame repr clause, prove the mutators transfer through it, then the
cold clauses (T3/T4) for restore_frame's discharge (D6).

Commit 20 (053caca) remains the fully-verified checkpoint beneath.


## D5 progress + the repr_ok open-frame clause (2026-09-13)

VERIFIED over the ghost trail (function-scoped, each 0 errors): set_index,
push, pop. The mutator template is proven three times - reconstruction
(frame_inv_range) and the capture bridge route through full_trail@ with the
unconditional discipline-free ghost append, triggers aligned to wf_for_snap
(g_end / snaps.len). The lemma family, wf/wf_for_snap, and the ghost model
are ported; ~2159 obligations verify.

REMAINING (the D5/D6 hard core, now pinned exactly): push_frame's
prepare_mark precondition - 'every set capture flag is named by a physical
diff_log suffix entry' - cannot be discharged from the ghost bridge alone,
because prepare_mark consumes the PHYSICAL diff_log open slice
[hot_top.start, diff_log.len()) while the bridge is over the GHOST open
stratum [g_start(top), full_trail.len()). Closing it needs repr_ok's
OPEN-FRAME clause:

  tf.len() > 0 ==> for the top frame, the physical diff_log open slice and
  the ghost open stratum carry the SAME SET OF INDICES (identity for the
  trail discipline; dedupe_first preserves the index set for unique
  capture).

This is the T1/T2 abstraction the goal's D5 names. It must be added to
repr_ok AND maintained by set_index/push/pop (each already verifies the
rest; this adds one clause to re-establish, provable from the capture
ensures: a first write adds the index to both, a duplicate leaves both
index sets unchanged). Then push_frame's prepare_mark and restore_frame's
discharge (D6) follow. NEXT SESSION: land the open-frame repr clause, thread
it through the three proven mutators, finish push_frame, then D6/D7.

Commit 20 (053caca) remains the fully-verified checkpoint beneath.


## D5 near-complete: 91 verified, push_frame the sole vec obligation (2026-09-13)

The ghost-model port of vec is essentially done: set_index, push, pop, the
whole lemma family (bounds/monotone/le_n/cell_eq/forks/saved_len),
maybe_shrink, with_store_mode, and the exec accessors ALL verify over
full_trail@ (91 obligations, 1 function left). Key fixes: single-trigger on
wf_for_snap's boundary-monotone clause; the mutator template (frame_inv_range
+ capture bridge over full_trail@, unconditional ghost append, aligned
triggers); forks/maybe_shrink pin the new stacks. repr_ok reverted to `true`
(its open-frame clause was the wrong mechanism - see below).

SOLE REMAINING vec obligation - push_frame's prepare_mark: it consumes the
PHYSICAL diff_log open slice, so it needs the PHYSICAL capture bridge
  captured()[j] <==> captured_in_range(diff_log@, hot_top.start, diff_log.len(), j)
which is a STORE-level fact (capture appends j to diff_log exactly when it
sets the flag; the flag persists). This is not a vec-local proof: it is a
DiffStore INTERFACE ADDITION - a spec fn + ensures on the trait, proved in
inline/parallel/trail store impls (each already maintains it; it was the
pre-ghost wf bridge). With it, push_frame's prepare_mark discharges
directly, and the ghost<->physical index-set equality becomes a derived
two-bridge consequence rather than a maintained invariant.

FINISH LINE (crisp):
  1. DiffStore: add fn captured_matches_log spec + ensures on capture/
     prepare_mark/begin_restore/finish_restore; prove in the 3 stores.
  2. push_frame: discharge prepare_mark from it; vec verifies 0 errors.
  3. D6: restore_frame + compress_all_hot + normalize/restore_run + the
     store restore_overlay loops - prove or trust-ledger (zero external_body
     on the restore path via the split_at_mut/copy_from_slice chain).
  4. D7: full 15-gate battery.

Commit 20 (053caca) remains the fully-verified baseline beneath.


## Confirmed: the dual-bridge is necessary (prepare_mark contract, 2026-09-13)

Reading prepare_mark's requires settles it: it quantifies 'every set flag j
is named by some prev_diffs entry' where prev_diffs is the PHYSICAL diff_log
slice [hot_top.start, diff_log.len()). The store does not own diff_log (vec
passes it by &mut), so the store's wf cannot state this - it is a JOINT
vec+store invariant that vec's wf must carry. push_frame's four residual
failures are exactly this: parent_diff_start (physical hot_top.start) !=
g_start(top) (ghost trail_frames[top]), and diff_start (physical) !=
full_trail.len() (ghost); the pre-tiering proof unified them because the
physical and ghost offsets coincided.

DEFINITIVE COMPLETION SPEC (one coherent refactor, not incremental):
  wf carries BOTH capture bridges over the OPEN (top) frame -
    physical:  captured()[j] == captured_in_range(diff_log@,  hot_top.start,        diff_log@.len(),  j)
    ghost:     captured()[j] == captured_in_range(full_trail@, g_start(top),         full_trail@.len(), j)
  The physical bridge (the pre-port clause) discharges push_frame's
  prepare_mark directly; the ghost bridge drives reconstruction. Their
  transitive consequence is the physical/ghost open-slice index-set
  equality - so repr_ok needs no open-frame clause. Restore the physical-
  bridge proof blocks in set_index/push/pop (they existed pre-port; git has
  them), add them beside the ghost blocks already proven, fix push_frame's
  physical/ghost split, then D6/D7. This is a single multi-function unit
  best applied and verified together, not left half-landed - which is why
  the committed checkpoint is held at 91/1 (a24f31e) rather than degraded.

Status: D1-D4 done; D5 at 91/1 in vec with the completion spec above; D6-D7
pending. cargo verus verify is NOT at 0 errors. Commit 20 (053caca, 15/15
gates) is the verified baseline.


## Dual-bridge state (2026-09-13): set_index+pop verified, 90/2 in vec

The dual-bridge architecture is landed and PROVEN for set_index and pop:
wf carries the physical capture bridge (over diff_log@/hot_top.start, for
prepare_mark) and the ghost bridge (over full_trail@, for reconstruction),
plus two structural invariants that surfaced and are true by construction:
hot-frame extent (hot_top.start <= diff_log.len()) and open-frame-is-hot
(tf.len()>0 ==> hot_stack.len()>0). 90 vec obligations verify.

REMAINING (2 vec functions, then D6/D7):
- push (1): its physical-bridge REENTERED case (j == old_len, a
  mark_captured into a popped-but-marked slot) is NOT a mechanical copy of
  the ghost case - it depends on whether the store appends the reentered
  index to the PHYSICAL diff_log (first-write in the new stratum). Needs the
  store capture/mark_captured postcondition, per discipline. The non-
  reentered part duplicates set_index's physical bridge cleanly.
- push_frame (17): the physical/ghost offset split - prepare_mark discharges
  from the physical bridge (now in wf); the wf re-establishment for the new
  empty frame follows the set_index template with g_start(new)=full_trail.len,
  hot_top.start=diff_log.len separately.
- D6: restore_frame/compress_all_hot/normalize/restore_run + store
  restore_overlay loops - prove or trust-ledger, zero external_body on the
  restore path.
- D7: 15-gate battery.

cargo verus verify NOT at 0 errors. Commit 20 (053caca, 15/15) is baseline.


## push reentered case: a design decision on the physical bridge (2026-09-13)

Diagnosed to root: mark_captured(i) only sets the flag
(captured().update(i,true)); it does NOT append to diff_log. So when push
reenters a popped-but-marked slot old_len, the log entry naming old_len
came from the EARLIER pop's capture and must still be present. The ghost
bridge proves captured_in_range(full_trail, old_len) via frame_inv_range's
captured arm (the reconstruction invariant, over full_trail). The physical
bridge needs captured_in_range(diff_log, old_len) - for which there is no
physical analog of frame_inv_range.

So the dual-bridge has an asymmetric maintenance cost: the physical bridge's
reentered case is not derivable from the ghost bridge alone (that would be
circular with the index-set equality it is meant to support). The two clean
options, to decide before continuing:
  (A) add a PHYSICAL frame_inv_range clause to wf (doubles the
      reconstruction invariant, but every mutator proof already has the
      ghost version as a template);
  (B) prove an index-set-PRESERVATION lemma across pop/push (the physical
      and ghost open slices gain/lose the same indices per op) and derive
      the physical bridge from the ghost one + that lemma.
(B) is less duplication but a genuinely new inductive lemma; (A) is more
mechanical. This is the one remaining DESIGN choice; set_index (no reenter)
and pop already verify with the dual bridge, so the non-reentered paths are
settled either way.

Definitive remaining after the choice: push (reentered), push_frame (offset
split, discharges from the physical bridge), D6 (restore-path discharge),
D7 (battery). cargo verus verify NOT at 0 errors; commit 20 (053caca,
15/15) is the verified baseline.

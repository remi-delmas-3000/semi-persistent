//! The typed external history manager (`group::ForkHistory<M>`): a group of
//! one column, a pair of columns driven as one, the lockstep theorem at
//! runtime, and the refusals (drift behind the group's back, foreign and
//! dead tokens, adopting a member that already has frames).

use semi_persistent_containers_verus::append_only_vec::AppendOnlyVec;
use semi_persistent_containers_verus::bplus::BPlusTreeSet;
use semi_persistent_containers_verus::bplus_layout::Layout64U32;
use semi_persistent_containers_verus::bplus_search::BinarySearch;
use semi_persistent_containers_verus::circular_list::CircularList;
use semi_persistent_containers_verus::dense_id::{DenseId31, DenseId63};
use semi_persistent_containers_verus::eclasses::EClasses;
use semi_persistent_containers_verus::group::{ForkHistory, Member, Pair};
use semi_persistent_containers_verus::index_like::IndexLike;
use semi_persistent_containers_verus::list::ListArena;
use semi_persistent_containers_verus::map::SpMap;
use semi_persistent_containers_verus::opt::DenseId;
use semi_persistent_containers_verus::sparse_set::SparseSet;
use semi_persistent_containers_verus::union_find::{NoJust, UnionFind};
use semi_persistent_containers_verus::{ParallelStore, ShrinkPolicy, VecP};

semi_persistent_containers_verus::define_id31! {
    pub struct GroupClassKey / StoredGroupClassKey, "gk";
}

type Col = VecP<u32, u32, true>;
type Log = AppendOnlyVec<u64, u32, true>;

fn col(n: u32) -> Col {
    let mut v = Col::new();
    for i in 0..n {
        v.try_push(i).unwrap();
    }
    v
}

fn vals(v: &Col) -> Vec<u32> {
    (0..v.len()).map(|i| v.get(i)).collect()
}

#[test]
fn group_of_one_marks_restores_and_pops_in_lockstep() {
    let mut g = ForkHistory::new(col(4));
    assert_eq!(g.depth(), 0);
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.set(0u32, 9);
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.set(1u32, 9);
    assert_eq!(g.depth(), 2);
    assert_eq!(g.member.depth(), 2);
    assert!(g.in_lockstep());

    // Semantics B: back to the checkpoint, its frame stays open, the token
    // stays valid and can be restored to again.
    assert!(g.restore(t1));
    assert_eq!(vals(&g.member), vec![9, 1, 2, 3]);
    assert_eq!(g.depth(), 2);
    assert!(g.is_valid(t1));
    g.member.set(2u32, 9);
    assert!(g.restore(t1));
    assert_eq!(vals(&g.member), vec![9, 1, 2, 3]);

    // The pop drops that frame and kills its token; the ancestor survives.
    assert!(g.pop());
    assert_eq!(g.depth(), 1);
    assert!(!g.is_valid(t1));
    assert!(g.is_valid(t0));
    assert!(!g.restore(t1));

    // The fused pop lands at the token's depth and kills it.
    assert!(g.restore_and_pop(t0));
    assert_eq!(vals(&g.member), vec![0, 1, 2, 3]);
    assert_eq!(g.depth(), 0);
    assert_eq!(g.member.depth(), 0);
    assert!(!g.is_valid(t0));
    assert!(!g.restore(t0));
    assert!(!g.restore_and_pop(t0));
    assert!(!g.pop(), "nothing to pop");
}

#[test]
fn a_frame_pushed_behind_the_groups_back_is_refused_until_repaired() {
    let mut g = ForkHistory::new(col(2));
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.set(0u32, 5);
    // Drift: the member's own frame stack moves without the group.
    g.member.push_frame(ShrinkPolicy::Never);
    assert!(!g.in_lockstep());
    assert!(g.mark(ShrinkPolicy::Never).is_none());
    assert!(!g.restore(t0));
    assert!(!g.restore_and_pop(t0));
    assert!(!g.pop());
    assert_eq!(vals(&g.member), vec![5, 1], "a refusal changes nothing");
    // Repair the drift and the group answers again.
    g.member.pop_frame();
    assert!(g.in_lockstep());
    assert!(g.restore(t0));
    assert_eq!(vals(&g.member), vec![0, 1]);
    assert_eq!(g.depth(), 1);
}

#[test]
fn foreign_tokens_are_refused() {
    let mut a = ForkHistory::new(col(1));
    let mut b = ForkHistory::new(col(1));
    let tb = b.mark(ShrinkPolicy::Never).expect("mark");
    let ta = a.mark(ShrinkPolicy::Never).expect("mark");
    assert!(!a.is_valid(tb));
    assert!(!a.restore(tb));
    assert!(!a.restore_and_pop(tb));
    assert!(a.is_valid(ta));
    assert!(b.is_valid(tb));
    assert!(!b.is_valid(ta));
}

#[test]
fn a_pair_of_columns_moves_as_one() {
    let mut g = ForkHistory::new(Pair::new(col(2), Log::new()));
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.a.set(0u32, 7);
    g.member.b.try_push(42).unwrap();
    g.member.b.try_push(43).unwrap();
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.a.set(1u32, 8);
    g.member.b.try_push(44).unwrap();
    assert_eq!(g.member.a.depth(), 2);
    assert_eq!(g.member.b.depth(), 2);

    assert!(g.restore(t1));
    assert_eq!(vals(&g.member.a), vec![7, 1]);
    assert_eq!(g.member.b.as_slice(), &[42, 43]);
    assert_eq!(g.depth(), 2);

    assert!(g.restore_and_pop(t0));
    assert_eq!(vals(&g.member.a), vec![0, 1]);
    assert!(g.member.b.as_slice().is_empty());
    assert_eq!(g.depth(), 0);
    assert_eq!(g.member.a.depth(), 0);
    assert_eq!(g.member.b.depth(), 0);
}

#[test]
#[should_panic(expected = "already has open frames")]
fn adopting_a_member_with_open_frames_is_refused() {
    let mut v = col(1);
    v.try_mark(ShrinkPolicy::Never).unwrap();
    let _g = ForkHistory::new(v);
}

#[test]
#[should_panic(expected = "not at the same depth")]
fn pairing_members_out_of_step_is_refused() {
    let mut v = col(1);
    v.try_mark(ShrinkPolicy::Never).unwrap();
    let _p = Pair::new(v, Log::new());
}

// ---------------------------------------------------------------------------
// Composites as members: the same group protocol over their token-free cores.
// ---------------------------------------------------------------------------

#[test]
fn a_sparse_set_is_a_member() {
    let mut g = ForkHistory::new(SparseSet::<u32, u32, ParallelStore<u32, u32>, true>::new());
    let a = g.member.try_add(10).unwrap();
    let b = g.member.try_add(20).unwrap();
    let c = g.member.try_add(30).unwrap();
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.remove(b);
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark");
    let d = g.member.try_add(40).unwrap();
    assert!(g.member.contains(d));
    assert_eq!(g.depth(), 2);

    assert!(g.restore(t1));
    assert!(g.member.contains(a) && !g.member.contains(b) && g.member.contains(c));
    assert_eq!(g.member.len().as_usize(), 2);
    assert_eq!(g.depth(), 2);
    assert!(g.is_valid(t1), "semantics B: the checkpoint stays valid");

    assert!(g.restore_and_pop(t0));
    assert!(g.member.contains(a) && g.member.contains(b) && g.member.contains(c));
    assert_eq!(g.member.len().as_usize(), 3);
    assert_eq!(g.depth(), 0);
    assert!(!g.is_valid(t0) && !g.is_valid(t1));
}

#[test]
fn a_ring_is_a_member() {
    let mut g = ForkHistory::new(CircularList::<u32, DenseId63, true>::new());
    let a = g.member.try_add_singleton(1).unwrap();
    let b = g.member.try_add_singleton(2).unwrap();
    let c = g.member.try_add_singleton(3).unwrap();
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.splice(a, b);
    g.member.splice(a, c);
    assert_ne!(
        g.member.next_of(a).to_usize(),
        a.to_usize(),
        "a's ring grew"
    );
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.set_payload(a, 100);

    assert!(g.restore(t1));
    assert_eq!(g.member.payload_of(a), 1);
    assert_ne!(g.member.next_of(a).to_usize(), a.to_usize());
    assert!(g.is_valid(t1));

    assert!(g.restore_and_pop(t0));
    assert_eq!(
        g.member.next_of(a).to_usize(),
        a.to_usize(),
        "singletons again"
    );
    assert_eq!(g.member.next_of(b).to_usize(), b.to_usize());
    assert_eq!(g.member.len().as_usize(), 3);
    assert_eq!(g.depth(), 0);
    assert!(!g.is_valid(t0));
}

#[test]
fn a_list_arena_is_a_member() {
    let mut g = ForkHistory::new(ListArena::<u32, DenseId63, DenseId63, true>::new());
    let l = g.member.try_new_list().unwrap();
    g.member.try_append(l, 1).unwrap();
    g.member.try_append(l, 2).unwrap();
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.try_append(l, 3).unwrap();
    assert_eq!(g.member.len(l).as_usize(), 3);

    assert!(g.restore(t0));
    assert_eq!(g.member.len(l).as_usize(), 2);
    g.member.try_append(l, 4).unwrap();
    assert_eq!(g.member.len(l).as_usize(), 3);
    assert!(g.restore(t0), "the checkpoint is reusable");
    assert_eq!(g.member.len(l).as_usize(), 2);
    assert_eq!(g.depth(), 1);

    assert!(g.pop());
    assert_eq!(g.member.len(l).as_usize(), 2);
    assert_eq!(g.depth(), 0);
    assert!(!g.is_valid(t0));
    assert!(!g.restore(t0));
}

#[test]
fn a_union_find_is_a_member() {
    let mut g = ForkHistory::new(UnionFind::<DenseId63, NoJust, true, false>::new());
    let a = g.member.try_make_set().unwrap();
    let b = g.member.try_make_set().unwrap();
    let c = g.member.try_make_set().unwrap();
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.union(a, b);
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.union(b, c);
    assert_eq!(
        g.member.find_const(a).to_usize(),
        g.member.find_const(c).to_usize()
    );

    assert!(g.restore(t1));
    assert_eq!(
        g.member.find_const(a).to_usize(),
        g.member.find_const(b).to_usize()
    );
    assert_ne!(
        g.member.find_const(a).to_usize(),
        g.member.find_const(c).to_usize()
    );
    assert_eq!(g.depth(), 2);
    assert!(g.is_valid(t1));
    g.member.union(a, c);
    assert!(g.restore(t1), "the checkpoint is reusable");
    assert_ne!(
        g.member.find_const(a).to_usize(),
        g.member.find_const(c).to_usize()
    );

    assert!(g.restore_and_pop(t0));
    assert_ne!(
        g.member.find_const(a).to_usize(),
        g.member.find_const(b).to_usize()
    );
    assert_eq!(g.member.len().as_usize(), 3);
    assert_eq!(g.depth(), 0);
    assert!(!g.is_valid(t0) && !g.is_valid(t1));
}

#[test]
fn a_map_is_a_member() {
    let mut g = ForkHistory::new(SpMap::<u64, (), usize, true>::new());
    for k in 0..8u64 {
        g.member.try_insert(k, ()).unwrap();
    }
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    for k in 100..104u64 {
        g.member.try_insert(k, ()).unwrap();
    }
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.try_insert(200, ()).unwrap();
    assert_eq!(g.member.len(), 13);

    assert!(g.restore(t1));
    assert_eq!(g.member.len(), 12);
    assert!(g.member.contains_key(&103) && !g.member.contains_key(&200));
    assert!(g.is_valid(t1));
    g.member.try_insert(300, ()).unwrap();
    assert!(g.restore(t1), "the checkpoint is reusable");
    assert_eq!(g.member.len(), 12);

    assert!(g.restore_and_pop(t0));
    assert_eq!(g.member.len(), 8);
    assert!(!g.member.contains_key(&100));
    assert_eq!(g.depth(), 0);
    assert!(!g.is_valid(t0) && !g.is_valid(t1));
}

#[test]
fn a_bplus_tree_is_a_member() {
    let mut g = ForkHistory::new(BPlusTreeSet::<DenseId31, Layout64U32, BinarySearch, true>::new());
    for k in 0..40u32 {
        g.member.try_insert(DenseId31::new(k)).unwrap();
    }
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    for k in 100..130u32 {
        g.member.try_insert(DenseId31::new(k)).unwrap();
    }
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.try_insert(DenseId31::new(500)).unwrap();
    assert_eq!(g.member.len(), 71);

    assert!(g.restore(t1));
    assert_eq!(g.member.len(), 70);
    assert!(g.member.contains(DenseId31::new(129)) && !g.member.contains(DenseId31::new(500)));
    assert!(g.is_valid(t1));
    g.member.try_insert(DenseId31::new(600)).unwrap();
    assert!(g.restore(t1), "the checkpoint is reusable");
    assert_eq!(g.member.len(), 70);

    assert!(g.restore_and_pop(t0));
    assert_eq!(g.member.len(), 40);
    assert!(!g.member.contains(DenseId31::new(100)));
    assert_eq!(g.depth(), 0);
    assert!(!g.is_valid(t0) && !g.is_valid(t1));
}

#[test]
fn e_classes_are_a_member() {
    let mut g = ForkHistory::new(EClasses::<
        DenseId31,
        GroupClassKey,
        DenseId31,
        DenseId31,
        NoJust,
        true,
        false,
    >::new());
    let (a, _) = g.member.try_add_singleton();
    let (b, _) = g.member.try_add_singleton();
    let (c, _) = g.member.try_add_singleton();
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.merge(a, b);
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.merge(b, c);
    assert_eq!(g.member.num_classes().as_usize(), 1);

    assert!(g.restore(t1));
    assert_eq!(g.member.num_classes().as_usize(), 2);
    assert_eq!(
        g.member.find_const(a).to_usize(),
        g.member.find_const(b).to_usize()
    );
    assert_ne!(
        g.member.find_const(a).to_usize(),
        g.member.find_const(c).to_usize()
    );
    assert!(g.is_valid(t1));
    g.member.merge(a, c);
    assert!(g.restore(t1), "the checkpoint is reusable");
    assert_eq!(g.member.num_classes().as_usize(), 2);

    assert!(g.restore_and_pop(t0));
    assert_eq!(g.member.num_classes().as_usize(), 3);
    assert_eq!(g.depth(), 0);
    assert!(!g.is_valid(t0) && !g.is_valid(t1));
}

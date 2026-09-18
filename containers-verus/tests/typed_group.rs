//! The typed external history manager (`group::ForkHistory<M>`): a group of
//! one column, a pair of columns driven as one, the lockstep theorem at
//! runtime, and the refusals (drift behind the group's back, foreign and
//! dead tokens, adopting a member that already has frames).

use semi_persistent_containers_verus::append_only_vec::AppendOnlyVec;
use semi_persistent_containers_verus::group::{ForkHistory, Member, Pair};
use semi_persistent_containers_verus::{ShrinkPolicy, VecP};

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

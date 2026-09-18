//! `restore_and_pop(t)` is `restore(t)` then `pop_scope()`, fused (design doc
//! 08 §1): same contents, same depth, same token fate — on one pop core, so it
//! costs what the legacy restore costs. These tests pin the equivalence on a
//! column and a composite, the depth and token fate, and the refusal path.

use semi_persistent_containers_verus::error::ContainerError;
use semi_persistent_containers_verus::map::SpMap;
use semi_persistent_containers_verus::{ShrinkPolicy, VecP};

type V = VecP<u64, u32, true>;
type M = SpMap<u64, (), usize, true>;

fn column(n: u64) -> V {
    let mut v = V::new();
    for i in 0..n {
        v.try_push(i).unwrap();
    }
    v
}

fn values(v: &V) -> Vec<u64> {
    (0..v.len()).map(|i| v.get(i)).collect()
}

#[test]
fn fused_equals_restore_then_pop_on_a_column() {
    let mut a = column(8);
    let mut b = column(8);
    let ta = a.try_mark(ShrinkPolicy::Never).unwrap();
    let tb = b.try_mark(ShrinkPolicy::Never).unwrap();
    for v in [&mut a, &mut b] {
        v.set(1u32, 100);
        v.try_push(200).unwrap();
        v.try_mark(ShrinkPolicy::Never).unwrap();
        v.set(2u32, 300);
    }
    assert_eq!(a.depth(), 2);

    a.try_restore(ta).unwrap();
    assert!(a.is_valid_token(&ta), "restore keeps the checkpoint open");
    a.pop_scope();
    b.try_restore_and_pop(tb).unwrap();

    assert_eq!(values(&a), values(&b));
    assert_eq!(values(&b), (0..8u64).collect::<Vec<_>>());
    assert_eq!(a.depth(), 0);
    assert_eq!(b.depth(), 0);
    assert!(!a.is_valid_token(&ta), "the pop kills the checkpoint");
    assert!(!b.is_valid_token(&tb), "the fused op kills the checkpoint");
    assert_eq!(b.try_restore_and_pop(tb), Err(ContainerError::InvalidToken));
    assert_eq!(b.try_restore(tb), Err(ContainerError::InvalidToken));
}

#[test]
fn fused_op_lands_at_the_token_depth_and_kills_deeper_tokens() {
    let mut v = column(4);
    let t0 = v.try_mark(ShrinkPolicy::Never).unwrap();
    v.set(0u32, 9);
    let t1 = v.try_mark(ShrinkPolicy::Never).unwrap();
    v.set(1u32, 9);
    let t2 = v.try_mark(ShrinkPolicy::Never).unwrap();
    v.set(2u32, 9);
    assert_eq!(v.depth(), 3);

    v.try_restore_and_pop(t1).unwrap();
    assert_eq!(v.depth(), 1, "frame t1 and everything above it are gone");
    assert_eq!(values(&v), vec![9, 1, 2, 3]);
    assert!(v.is_valid_token(&t0), "the ancestor survives");
    assert!(!v.is_valid_token(&t1));
    assert!(!v.is_valid_token(&t2));
    // A fresh mark at depth 1 mints a new stamp: the old t1 never revives.
    let t1b = v.try_mark(ShrinkPolicy::Never).unwrap();
    assert!(!v.is_valid_token(&t1));
    assert!(v.is_valid_token(&t1b));
    v.try_restore_and_pop(t0).unwrap();
    assert_eq!(v.depth(), 0);
    assert_eq!(values(&v), vec![0, 1, 2, 3]);
}

#[test]
fn fused_op_refuses_a_foreign_token_without_mutating() {
    let mut a = column(3);
    let mut b = column(3);
    let tb = b.try_mark(ShrinkPolicy::Never).unwrap();
    a.try_mark(ShrinkPolicy::Never).unwrap();
    a.set(0u32, 7);
    assert_eq!(a.try_restore_and_pop(tb), Err(ContainerError::InvalidToken));
    assert_eq!(values(&a), vec![7, 1, 2]);
    assert_eq!(a.depth(), 1);
}

#[test]
fn fused_equals_restore_then_pop_on_a_map() {
    let mut a: M = SpMap::new();
    let mut b: M = SpMap::new();
    for m in [&mut a, &mut b] {
        for k in 0..16u64 {
            m.try_insert(k, ()).unwrap();
        }
    }
    let ta = a.try_mark(ShrinkPolicy::Never).unwrap();
    let tb = b.try_mark(ShrinkPolicy::Never).unwrap();
    for m in [&mut a, &mut b] {
        for k in 100..140u64 {
            m.try_insert(k, ()).unwrap();
        }
    }
    a.try_restore(ta).unwrap();
    a.pop_scope();
    b.try_restore_and_pop(tb).unwrap();
    assert_eq!(a.len(), b.len());
    assert_eq!(a.len(), 16);
    assert_eq!(a.depth(), 0);
    assert_eq!(b.depth(), 0);
    for k in 0..16u64 {
        assert!(a.contains_key(&k) && b.contains_key(&k));
    }
    assert!(!a.contains_key(&120) && !b.contains_key(&120));
    assert_eq!(b.try_restore_and_pop(tb), Err(ContainerError::InvalidToken));
}

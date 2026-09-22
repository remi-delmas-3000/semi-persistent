// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Codegen probe for the composite containers (see `codegen_probe.rs` for the
//! Vec probes and the method): one `#[inline(never)]` function per
//! (container, mode, method), verified and legacy side by side.
//!
//! Build: `cargo build --release -p containers-conformance --example codegen_probe_composites`
//! then run `tools/codegen_audit.py target/release/examples/codegen_probe_composites`.
#![allow(clippy::all)]

use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::hint::black_box;
use verus::group::ForkHistory;
use verus::vec::ShrinkPolicy;

prod::define_id31! { pub struct PElem / StoredPElem, "e"; }
prod::define_id31! { pub struct PList / StoredPList, "l"; }
prod::define_id31! { pub struct PNode / StoredPNode, "n"; }
prod::define_id31! { pub struct PId / StoredPId, "p"; }
prod::define_id31! { pub struct RE / StoredRE, "re"; }
prod::define_id31! { pub struct RK / StoredRK, "rk"; }
prod::define_id31! { pub struct RL / StoredRL, "rl"; }
prod::define_id31! { pub struct RN / StoredRN, "rn"; }
verus::define_id31! { pub struct VElem / StoredVElem, "e"; }
verus::define_id31! { pub struct VList / StoredVList, "l"; }
verus::define_id31! { pub struct VNode / StoredVNode, "n"; }
verus::define_id31! { pub struct VId / StoredVId, "v"; }
verus::define_id31! { pub struct VE / StoredVE, "ve"; }
verus::define_id31! { pub struct VK / StoredVK, "vk"; }
verus::define_id31! { pub struct VL / StoredVL, "vl"; }
verus::define_id31! { pub struct VN / StoredVN, "vn"; }
verus::define_id31! { pub struct VRingNode / StoredVRingNode, "r"; }
verus::define_id31! { pub struct VRingKey / StoredVRingKey, "rk"; }

const LISTS: usize = 512;
const PER_LIST: usize = 16;
const N: usize = 4096;
const OPS: usize = 8192;

// ---------------------------------------------------------------------------
// ListArena
// ---------------------------------------------------------------------------

macro_rules! list_probes {
    ($track:literal, $tag:ident) => {
        pub mod $tag {
            use super::*;
            type VA = verus::ListArena<VElem, VList, VNode, $track>;
            type PA = prod::ListArena<PElem, PList, PNode, $track>;

            fn fresh_v() -> (VA, Vec<VList>) {
                let mut a = VA::new();
                let mut ls = Vec::with_capacity(LISTS);
                for _ in 0..LISTS {
                    ls.push(a.try_new_list().expect("ids"));
                }
                for (k, &l) in ls.iter().enumerate() {
                    for j in 0..PER_LIST {
                        a.try_append(l, VElem::new((k * PER_LIST + j) as u32))
                            .expect("ids");
                    }
                }
                (a, ls)
            }
            fn fresh_p() -> (PA, Vec<PList>) {
                let mut a = PA::new();
                let mut ls = Vec::with_capacity(LISTS);
                for _ in 0..LISTS {
                    ls.push(a.new_list());
                }
                for (k, &l) in ls.iter().enumerate() {
                    for j in 0..PER_LIST {
                        a.append(l, PElem::new((k * PER_LIST + j) as u32));
                    }
                }
                (a, ls)
            }

            #[inline(never)]
            pub fn probe_list_append_v(n: usize) -> u64 {
                let mut a = VA::new();
                let l = a.try_new_list().expect("ids");
                for i in 0..n {
                    a.try_append(l, VElem::new(i as u32)).expect("ids");
                }
                a.len(l) as u64
            }
            #[inline(never)]
            pub fn probe_list_append_p(n: usize) -> u64 {
                let mut a = PA::new();
                let l = a.new_list();
                for i in 0..n {
                    a.append(l, PElem::new(i as u32));
                }
                a.len(l) as u64
            }
            #[inline(never)]
            pub fn probe_list_prepend_v(n: usize) -> u64 {
                let mut a = VA::new();
                let l = a.try_new_list().expect("ids");
                for i in 0..n {
                    a.try_prepend(l, VElem::new(i as u32)).expect("ids");
                }
                a.len(l) as u64
            }
            #[inline(never)]
            pub fn probe_list_prepend_p(n: usize) -> u64 {
                let mut a = PA::new();
                let l = a.new_list();
                for i in 0..n {
                    a.prepend(l, PElem::new(i as u32));
                }
                a.len(l) as u64
            }
            #[inline(never)]
            pub fn probe_list_iter_v(n: usize) -> u64 {
                let (a, ls) = fresh_v();
                let mut acc = 0u64;
                for _ in 0..n / (LISTS * PER_LIST) + 1 {
                    for &l in &ls {
                        for e in a.iter(l) {
                            acc = acc.wrapping_add(e.raw() as u64);
                        }
                    }
                }
                acc
            }
            #[inline(never)]
            pub fn probe_list_iter_p(n: usize) -> u64 {
                let (a, ls) = fresh_p();
                let mut acc = 0u64;
                for _ in 0..n / (LISTS * PER_LIST) + 1 {
                    for &l in &ls {
                        for e in a.iter(l) {
                            acc = acc.wrapping_add(e.raw() as u64);
                        }
                    }
                }
                acc
            }
            #[inline(never)]
            pub fn probe_list_splice_v(n: usize) -> u64 {
                let (mut a, ls) = fresh_v();
                let mut acc = 0u64;
                for k in 0..n.min(LISTS - 1) {
                    a.splice(ls[0], ls[k + 1]);
                    acc = acc.wrapping_add(a.len(ls[0]) as u64);
                }
                acc
            }
            #[inline(never)]
            pub fn probe_list_splice_p(n: usize) -> u64 {
                let (mut a, ls) = fresh_p();
                let mut acc = 0u64;
                for k in 0..n.min(LISTS - 1) {
                    a.splice(ls[0], ls[k + 1]);
                    acc = acc.wrapping_add(a.len(ls[0]) as u64);
                }
                acc
            }
            #[inline(never)]
            pub fn probe_list_mark_append_restore_v(n: usize) -> u64 {
                let (a, ls) = fresh_v();
                let mut a = ForkHistory::new(a);
                let mut acc = 0u64;
                for round in 0..n / 32 {
                    let t = a.mark(ShrinkPolicy::Never).expect("mark");
                    let l = ls[round % LISTS];
                    for j in 0..32 {
                        a.try_append(l, VElem::new(j)).expect("ids");
                    }
                    acc = acc.wrapping_add(a.len(l) as u64);
                    assert!(a.restore_and_pop(t));
                }
                acc
            }
            #[inline(never)]
            pub fn probe_list_mark_append_restore_p(n: usize) -> u64 {
                let (mut a, ls) = fresh_p();
                let mut acc = 0u64;
                for round in 0..n / 32 {
                    let t = a.mark(prod::ShrinkPolicy::Never);
                    let l = ls[round % LISTS];
                    for j in 0..32 {
                        a.append(l, PElem::new(j));
                    }
                    acc = acc.wrapping_add(a.len(l) as u64);
                    a.restore(t);
                }
                acc
            }

            pub fn run_all(n: usize) -> u64 {
                let mut acc = 0u64;
                acc = acc.wrapping_add(probe_list_append_v(black_box(n)));
                acc = acc.wrapping_add(probe_list_append_p(black_box(n)));
                acc = acc.wrapping_add(probe_list_prepend_v(black_box(n)));
                acc = acc.wrapping_add(probe_list_prepend_p(black_box(n)));
                acc = acc.wrapping_add(probe_list_iter_v(black_box(n)));
                acc = acc.wrapping_add(probe_list_iter_p(black_box(n)));
                acc = acc.wrapping_add(probe_list_splice_v(black_box(n)));
                acc = acc.wrapping_add(probe_list_splice_p(black_box(n)));
                if $track {
                    acc = acc.wrapping_add(probe_list_mark_append_restore_v(black_box(n)));
                    acc = acc.wrapping_add(probe_list_mark_append_restore_p(black_box(n)));
                }
                acc
            }
        }
    };
}
list_probes!(false, list_untracked);
list_probes!(true, list_tracked);

// ---------------------------------------------------------------------------
// SparseSet
// ---------------------------------------------------------------------------

macro_rules! sparse_probes {
    ($track:literal, $tag:ident) => {
        pub mod $tag {
            use super::*;
            type VS = verus::SparseSet<u64, VElem, verus::ParallelStore<u64, VElem>, $track>;
            type PS = prod::SparseSet<u64, PElem, prod::ParallelStore<u64, PElem>, $track>;

            fn fresh_v() -> (VS, Vec<VElem>) {
                let mut s = VS::new();
                let ids: Vec<VElem> = (0..N as u64).map(|i| s.try_add(i).expect("ids")).collect();
                (s, ids)
            }
            fn fresh_p() -> (PS, Vec<PElem>) {
                let mut s = PS::new();
                let ids: Vec<PElem> = (0..N as u64).map(|i| s.add(i)).collect();
                (s, ids)
            }

            #[inline(never)]
            pub fn probe_sparse_add_v(n: usize) -> u64 {
                let mut s = VS::new();
                let mut acc = 0u64;
                for i in 0..n as u64 {
                    acc = acc.wrapping_add(s.try_add(i).expect("ids").raw() as u64);
                }
                acc
            }
            #[inline(never)]
            pub fn probe_sparse_add_p(n: usize) -> u64 {
                let mut s = PS::new();
                let mut acc = 0u64;
                for i in 0..n as u64 {
                    acc = acc.wrapping_add(s.add(i).raw() as u64);
                }
                acc
            }
            #[inline(never)]
            pub fn probe_sparse_contains_get_v(n: usize) -> u64 {
                let (s, ids) = fresh_v();
                let mut acc = 0u64;
                for k in 0..n {
                    let id = ids[(k * 7) % N];
                    if s.contains(id) {
                        acc = acc.wrapping_add(s.get(id));
                    }
                }
                acc
            }
            #[inline(never)]
            pub fn probe_sparse_contains_get_p(n: usize) -> u64 {
                let (s, ids) = fresh_p();
                let mut acc = 0u64;
                for k in 0..n {
                    let id = ids[(k * 7) % N];
                    if s.contains(id) {
                        acc = acc.wrapping_add(s.get(id));
                    }
                }
                acc
            }
            #[inline(never)]
            pub fn probe_sparse_set_v(n: usize) -> u64 {
                let (mut s, ids) = fresh_v();
                for k in 0..n {
                    s.set(ids[(k * 7) % N], k as u64);
                }
                s.len().raw() as u64
            }
            #[inline(never)]
            pub fn probe_sparse_set_p(n: usize) -> u64 {
                let (mut s, ids) = fresh_p();
                for k in 0..n {
                    s.set(ids[(k * 7) % N], k as u64);
                }
                s.len().raw() as u64
            }
            #[inline(never)]
            pub fn probe_sparse_remove_add_v(n: usize) -> u64 {
                let (mut s, ids) = fresh_v();
                let mut acc = 0u64;
                for k in 0..n {
                    s.remove(ids[(k * 7) % N]);
                    acc = acc.wrapping_add(s.try_add(k as u64).expect("ids").raw() as u64);
                }
                acc
            }
            #[inline(never)]
            pub fn probe_sparse_remove_add_p(n: usize) -> u64 {
                let (mut s, ids) = fresh_p();
                let mut acc = 0u64;
                for k in 0..n {
                    s.remove(ids[(k * 7) % N]);
                    acc = acc.wrapping_add(s.add(k as u64).raw() as u64);
                }
                acc
            }
            #[inline(never)]
            pub fn probe_sparse_mark_churn_restore_v(n: usize) -> u64 {
                let (s, ids) = fresh_v();
                let mut s = ForkHistory::new(s);
                let mut acc = 0u64;
                for round in 0..n / 32 {
                    let t = s.mark(ShrinkPolicy::Never).expect("mark");
                    for j in 0..32 {
                        s.remove(ids[(round * 32 + j * 5) % N]);
                        s.try_add(j as u64).expect("ids");
                    }
                    acc = acc.wrapping_add(s.len().raw() as u64);
                    assert!(s.restore_and_pop(t));
                }
                acc
            }
            #[inline(never)]
            pub fn probe_sparse_mark_churn_restore_p(n: usize) -> u64 {
                let (mut s, ids) = fresh_p();
                let mut acc = 0u64;
                for round in 0..n / 32 {
                    let t = s.mark(prod::ShrinkPolicy::Never);
                    for j in 0..32 {
                        s.remove(ids[(round * 32 + j * 5) % N]);
                        s.add(j as u64);
                    }
                    acc = acc.wrapping_add(s.len().raw() as u64);
                    s.restore(t);
                }
                acc
            }

            pub fn run_all(n: usize) -> u64 {
                let mut acc = 0u64;
                acc = acc.wrapping_add(probe_sparse_add_v(black_box(n)));
                acc = acc.wrapping_add(probe_sparse_add_p(black_box(n)));
                acc = acc.wrapping_add(probe_sparse_contains_get_v(black_box(n)));
                acc = acc.wrapping_add(probe_sparse_contains_get_p(black_box(n)));
                acc = acc.wrapping_add(probe_sparse_set_v(black_box(n)));
                acc = acc.wrapping_add(probe_sparse_set_p(black_box(n)));
                acc = acc.wrapping_add(probe_sparse_remove_add_v(black_box(n)));
                acc = acc.wrapping_add(probe_sparse_remove_add_p(black_box(n)));
                if $track {
                    acc = acc.wrapping_add(probe_sparse_mark_churn_restore_v(black_box(n)));
                    acc = acc.wrapping_add(probe_sparse_mark_churn_restore_p(black_box(n)));
                }
                acc
            }
        }
    };
}
sparse_probes!(false, sparse_untracked);
sparse_probes!(true, sparse_tracked);

// ---------------------------------------------------------------------------
// AppendOnlyVec
// ---------------------------------------------------------------------------

macro_rules! aov_probes {
    ($track:literal, $tag:ident) => {
        pub mod $tag {
            use super::*;
            type VV = verus::AppendOnlyVec<u64, usize, $track>;
            type PV = prod::AppendOnlyVec<u64, usize, $track>;

            #[inline(never)]
            pub fn probe_aov_push_v(n: usize) -> u64 {
                let mut v = VV::new();
                let mut acc = 0u64;
                for i in 0..n as u64 {
                    acc = acc.wrapping_add(v.try_push(i).expect("capacity") as u64);
                }
                acc
            }
            #[inline(never)]
            pub fn probe_aov_push_p(n: usize) -> u64 {
                let mut v = PV::new();
                let mut acc = 0u64;
                for i in 0..n as u64 {
                    acc = acc.wrapping_add(v.push(i) as u64);
                }
                acc
            }
            #[inline(never)]
            pub fn probe_aov_get_v(n: usize) -> u64 {
                let mut v = VV::new();
                for i in 0..N as u64 {
                    v.try_push(i).expect("capacity");
                }
                let mut acc = 0u64;
                for k in 0..n {
                    acc = acc.wrapping_add(*v.get((k * 7) % N));
                }
                acc
            }
            #[inline(never)]
            pub fn probe_aov_get_p(n: usize) -> u64 {
                let mut v = PV::new();
                for i in 0..N as u64 {
                    v.push(i);
                }
                let mut acc = 0u64;
                for k in 0..n {
                    acc = acc.wrapping_add(*v.get((k * 7) % N));
                }
                acc
            }
            #[inline(never)]
            pub fn probe_aov_iter_v(n: usize) -> u64 {
                let mut v = VV::new();
                for i in 0..N as u64 {
                    v.try_push(i).expect("capacity");
                }
                let mut acc = 0u64;
                for _ in 0..n / N + 1 {
                    for x in v.iter() {
                        acc = acc.wrapping_add(*x);
                    }
                }
                acc
            }
            #[inline(never)]
            pub fn probe_aov_iter_p(n: usize) -> u64 {
                let mut v = PV::new();
                for i in 0..N as u64 {
                    v.push(i);
                }
                let mut acc = 0u64;
                for _ in 0..n / N + 1 {
                    for x in v.iter() {
                        acc = acc.wrapping_add(*x);
                    }
                }
                acc
            }
            #[inline(never)]
            pub fn probe_aov_mark_push_restore_v(n: usize) -> u64 {
                let mut v = ForkHistory::new(VV::new());
                let mut acc = 0u64;
                for round in 0..n / 32 {
                    let t = v.mark(ShrinkPolicy::Never).expect("mark");
                    for j in 0..32u64 {
                        v.try_push(j + round as u64).expect("capacity");
                    }
                    acc = acc.wrapping_add(v.len() as u64);
                    assert!(v.restore_and_pop(t));
                }
                acc
            }
            #[inline(never)]
            pub fn probe_aov_mark_push_restore_p(n: usize) -> u64 {
                let mut v = PV::new();
                let mut acc = 0u64;
                for round in 0..n / 32 {
                    let t = v.mark(prod::ShrinkPolicy::Never);
                    for j in 0..32u64 {
                        v.push(j + round as u64);
                    }
                    acc = acc.wrapping_add(v.len() as u64);
                    v.restore(t);
                }
                acc
            }

            pub fn run_all(n: usize) -> u64 {
                let mut acc = 0u64;
                acc = acc.wrapping_add(probe_aov_push_v(black_box(n)));
                acc = acc.wrapping_add(probe_aov_push_p(black_box(n)));
                acc = acc.wrapping_add(probe_aov_get_v(black_box(n)));
                acc = acc.wrapping_add(probe_aov_get_p(black_box(n)));
                acc = acc.wrapping_add(probe_aov_iter_v(black_box(n)));
                acc = acc.wrapping_add(probe_aov_iter_p(black_box(n)));
                if $track {
                    acc = acc.wrapping_add(probe_aov_mark_push_restore_v(black_box(n)));
                    acc = acc.wrapping_add(probe_aov_mark_push_restore_p(black_box(n)));
                }
                acc
            }
        }
    };
}
aov_probes!(false, aov_untracked);
aov_probes!(true, aov_tracked);

// ---------------------------------------------------------------------------
// SpMap / SpUniqueMap vs legacy Map
// ---------------------------------------------------------------------------

macro_rules! map_probes {
    ($track:literal, $tag:ident) => {
        pub mod $tag {
            use super::*;
            type VM = verus::SpMap<u64, u64, usize, $track>;
            type VU = verus::SpUniqueMap<u64, u64, usize, $track>;
            type PM = prod::Map<u64, u64, usize, $track>;

            #[inline(never)]
            pub fn probe_map_intern_v(n: usize) -> u64 {
                let mut m = VM::new();
                let mut acc = 0u64;
                for i in 0..n as u64 {
                    let (id, _fresh) = m.try_intern(i % 1024, i).expect("capacity");
                    acc = acc.wrapping_add(id as u64);
                }
                acc
            }
            #[inline(never)]
            pub fn probe_map_intern_unique_v(n: usize) -> u64 {
                let mut m = VU::new();
                let mut acc = 0u64;
                for i in 0..n as u64 {
                    let (id, _fresh) = m.try_intern(i % 1024, i).expect("capacity");
                    acc = acc.wrapping_add(id as u64);
                }
                acc
            }
            #[inline(never)]
            pub fn probe_map_intern_p(n: usize) -> u64 {
                let mut m = PM::new();
                let mut acc = 0u64;
                for i in 0..n as u64 {
                    let id = match m.id_of(&(i % 1024)) {
                        Some(id) => id,
                        None => m.insert(i % 1024, i),
                    };
                    acc = acc.wrapping_add(id as u64);
                }
                acc
            }
            #[inline(never)]
            pub fn probe_map_lookup_v(n: usize) -> u64 {
                let mut m = VU::new();
                for i in 0..1024u64 {
                    m.try_insert(i, i * 3).expect("capacity");
                }
                let mut acc = 0u64;
                for k in 0..n as u64 {
                    if let Some(v) = m.get_by_key(&(k % 2048)) {
                        acc = acc.wrapping_add(*v);
                    }
                    if m.contains_key(&(k % 1024)) {
                        acc = acc.wrapping_add(1);
                    }
                }
                acc
            }
            #[inline(never)]
            pub fn probe_map_lookup_p(n: usize) -> u64 {
                let mut m = PM::new();
                for i in 0..1024u64 {
                    m.insert(i, i * 3);
                }
                let mut acc = 0u64;
                for k in 0..n as u64 {
                    if let Some(v) = m.get_by_key(&(k % 2048)) {
                        acc = acc.wrapping_add(*v);
                    }
                    if m.contains_key(&(k % 1024)) {
                        acc = acc.wrapping_add(1);
                    }
                }
                acc
            }
            #[inline(never)]
            pub fn probe_map_mark_insert_restore_v(n: usize) -> u64 {
                let mut m = ForkHistory::new(VU::new());
                for i in 0..1024u64 {
                    m.try_insert(i, i).expect("capacity");
                }
                let mut acc = 0u64;
                for round in 0..n / 16 {
                    let t = m.mark(ShrinkPolicy::Never).expect("mark");
                    for j in 0..16u64 {
                        m.try_insert(100_000 + round as u64 * 16 + j, j)
                            .expect("capacity");
                    }
                    acc = acc.wrapping_add(m.len() as u64);
                    assert!(m.restore_and_pop(t));
                }
                acc
            }
            #[inline(never)]
            pub fn probe_map_mark_insert_restore_p(n: usize) -> u64 {
                let mut m = PM::new();
                for i in 0..1024u64 {
                    m.insert(i, i);
                }
                let mut acc = 0u64;
                for round in 0..n / 16 {
                    let t = m.mark(prod::ShrinkPolicy::Never);
                    for j in 0..16u64 {
                        m.insert(100_000 + round as u64 * 16 + j, j);
                    }
                    acc = acc.wrapping_add(m.len() as u64);
                    m.restore(t);
                }
                acc
            }

            pub fn run_all(n: usize) -> u64 {
                let mut acc = 0u64;
                acc = acc.wrapping_add(probe_map_intern_v(black_box(n)));
                acc = acc.wrapping_add(probe_map_intern_unique_v(black_box(n)));
                acc = acc.wrapping_add(probe_map_intern_p(black_box(n)));
                acc = acc.wrapping_add(probe_map_lookup_v(black_box(n)));
                acc = acc.wrapping_add(probe_map_lookup_p(black_box(n)));
                if $track {
                    acc = acc.wrapping_add(probe_map_mark_insert_restore_v(black_box(n)));
                    acc = acc.wrapping_add(probe_map_mark_insert_restore_p(black_box(n)));
                }
                acc
            }
        }
    };
}
map_probes!(false, map_untracked);
map_probes!(true, map_tracked);

// ---------------------------------------------------------------------------
// UnionFind
// ---------------------------------------------------------------------------

macro_rules! uf_probes {
    ($track:literal, $tag:ident) => {
        pub mod $tag {
            use super::*;
            type VU = verus::union_find::UnionFind<VElem, verus::union_find::NoJust, $track, false>;
            type PU = prod::union_find::UnionFind<PElem, prod::union_find::NoJust, $track, false>;

            fn fresh_v() -> (VU, Vec<VElem>) {
                let mut u = VU::new();
                let ids: Vec<VElem> = (0..N).map(|_| u.try_make_set().expect("ids")).collect();
                (u, ids)
            }
            fn fresh_p() -> (PU, Vec<PElem>) {
                let mut u = PU::new();
                let ids: Vec<PElem> = (0..N as u32)
                    .map(|i| {
                        let id = PElem::new(i);
                        u.make_set(id);
                        id
                    })
                    .collect();
                (u, ids)
            }

            #[inline(never)]
            pub fn probe_uf_union_find_v(n: usize) -> u64 {
                let (mut u, ids) = fresh_v();
                let mut acc = 0u64;
                for k in 0..n {
                    let a = ids[(k * 7) % N];
                    let b = ids[(k * 13 + 1) % N];
                    if u.union(a, b).is_some() {
                        acc = acc.wrapping_add(1);
                    }
                    acc = acc.wrapping_add(u.find(a).raw() as u64);
                }
                acc
            }
            #[inline(never)]
            pub fn probe_uf_union_find_p(n: usize) -> u64 {
                let (mut u, ids) = fresh_p();
                let mut acc = 0u64;
                for k in 0..n {
                    let a = ids[(k * 7) % N];
                    let b = ids[(k * 13 + 1) % N];
                    if u.union(a, b).is_some() {
                        acc = acc.wrapping_add(1);
                    }
                    acc = acc.wrapping_add(u.find(a).raw() as u64);
                }
                acc
            }
            #[inline(never)]
            pub fn probe_uf_find_const_v(n: usize) -> u64 {
                let (mut u, ids) = fresh_v();
                for k in 0..N - 1 {
                    u.union(ids[k], ids[k + 1]);
                }
                let mut acc = 0u64;
                for k in 0..n {
                    acc = acc.wrapping_add(u.find_const(ids[(k * 7) % N]).raw() as u64);
                }
                acc
            }
            #[inline(never)]
            pub fn probe_uf_find_const_p(n: usize) -> u64 {
                let (mut u, ids) = fresh_p();
                for k in 0..N - 1 {
                    u.union(ids[k], ids[k + 1]);
                }
                let mut acc = 0u64;
                for k in 0..n {
                    acc = acc.wrapping_add(u.find_const(ids[(k * 7) % N]).raw() as u64);
                }
                acc
            }
            #[inline(never)]
            pub fn probe_uf_mark_union_restore_v(n: usize) -> u64 {
                let (u, ids) = fresh_v();
                let mut u = ForkHistory::new(u);
                let mut acc = 0u64;
                for round in 0..n / 32 {
                    let t = u.mark(ShrinkPolicy::Never).expect("mark");
                    for j in 0..32 {
                        u.union(ids[(round + j * 5) % N], ids[(round + j * 11 + 1) % N]);
                    }
                    acc = acc.wrapping_add(u.find(ids[round % N]).raw() as u64);
                    assert!(u.restore_and_pop(t));
                }
                acc
            }
            #[inline(never)]
            pub fn probe_uf_mark_union_restore_p(n: usize) -> u64 {
                let (mut u, ids) = fresh_p();
                let mut acc = 0u64;
                for round in 0..n / 32 {
                    let t = u.mark(prod::ShrinkPolicy::Never);
                    for j in 0..32 {
                        u.union(ids[(round + j * 5) % N], ids[(round + j * 11 + 1) % N]);
                    }
                    acc = acc.wrapping_add(u.find(ids[round % N]).raw() as u64);
                    u.restore(t);
                }
                acc
            }

            pub fn run_all(n: usize) -> u64 {
                let mut acc = 0u64;
                acc = acc.wrapping_add(probe_uf_union_find_v(black_box(n)));
                acc = acc.wrapping_add(probe_uf_union_find_p(black_box(n)));
                acc = acc.wrapping_add(probe_uf_find_const_v(black_box(n)));
                acc = acc.wrapping_add(probe_uf_find_const_p(black_box(n)));
                if $track {
                    acc = acc.wrapping_add(probe_uf_mark_union_restore_v(black_box(n)));
                    acc = acc.wrapping_add(probe_uf_mark_union_restore_p(black_box(n)));
                }
                acc
            }
        }
    };
}
uf_probes!(false, uf_untracked);
uf_probes!(true, uf_tracked);

// ---------------------------------------------------------------------------
// EClasses (tracked only: the aggregate the e-graph uses)
// ---------------------------------------------------------------------------

pub mod eclasses_tracked {
    use super::*;
    type VEC = verus::eclasses::EClasses<VE, VK, VL, VN, verus::union_find::NoJust, true, false>;
    type PEC = prod::eclasses::EClasses<RE, RK, RL, RN, prod::union_find::NoJust, true, false>;

    fn fresh_v() -> (ForkHistory<VEC>, Vec<VE>) {
        let mut ec = ForkHistory::new(VEC::new());
        let mut ids = Vec::with_capacity(N);
        for _ in 0..N {
            let (id, key) = ec.try_add_singleton();
            ec.add_use(key, id);
            ids.push(id);
        }
        (ec, ids)
    }
    fn fresh_p() -> (PEC, Vec<RE>) {
        let mut ec = PEC::new();
        let mut ids = Vec::with_capacity(N);
        for i in 0..N as u32 {
            let id = RE::new(i);
            let key = ec.add_singleton(id);
            ec.add_use(key, id);
            ids.push(id);
        }
        (ec, ids)
    }

    #[inline(never)]
    pub fn probe_ec_add_singleton_use_v(n: usize) -> u64 {
        let mut ec = ForkHistory::new(VEC::new());
        let mut acc = 0u64;
        for _ in 0..n {
            let (id, key) = ec.try_add_singleton();
            ec.add_use(key, id);
            acc = acc.wrapping_add(id.raw() as u64);
        }
        acc
    }
    #[inline(never)]
    pub fn probe_ec_add_singleton_use_p(n: usize) -> u64 {
        let mut ec = PEC::new();
        let mut acc = 0u64;
        for i in 0..n as u32 {
            let id = RE::new(i);
            let key = ec.add_singleton(id);
            ec.add_use(key, id);
            acc = acc.wrapping_add(id.raw() as u64);
        }
        acc
    }
    #[inline(never)]
    pub fn probe_ec_find_v(n: usize) -> u64 {
        let (mut ec, ids) = fresh_v();
        let mut acc = 0u64;
        for k in 0..n {
            acc = acc.wrapping_add(ec.find(ids[(k * 7) % N]).raw() as u64);
        }
        acc
    }
    #[inline(never)]
    pub fn probe_ec_find_p(n: usize) -> u64 {
        let (mut ec, ids) = fresh_p();
        let mut acc = 0u64;
        for k in 0..n {
            acc = acc.wrapping_add(ec.find(ids[(k * 7) % N]).raw() as u64);
        }
        acc
    }
    #[inline(never)]
    pub fn probe_ec_merge_v(n: usize) -> u64 {
        let (mut ec, ids) = fresh_v();
        let mut acc = 0u64;
        for k in 0..n.min(N - 1) {
            if ec.merge(ids[k], ids[k + 1]).is_some() {
                acc = acc.wrapping_add(1);
            }
        }
        acc
    }
    #[inline(never)]
    pub fn probe_ec_merge_p(n: usize) -> u64 {
        let (mut ec, ids) = fresh_p();
        let mut acc = 0u64;
        for k in 0..n.min(N - 1) {
            if ec.merge(ids[k], ids[k + 1]).is_some() {
                acc = acc.wrapping_add(1);
            }
        }
        acc
    }
    #[inline(never)]
    pub fn probe_ec_mark_merge_restore_v(n: usize) -> u64 {
        let (mut ec, ids) = fresh_v();
        let mut acc = 0u64;
        for round in 0..n / 16 {
            let t = ec.mark(ShrinkPolicy::Never).expect("mark");
            for j in 0..16 {
                ec.merge(ids[(round + j * 5) % N], ids[(round + j * 11 + 1) % N]);
            }
            acc = acc.wrapping_add(ec.find(ids[round % N]).raw() as u64);
            assert!(ec.restore_and_pop(t));
        }
        acc
    }
    #[inline(never)]
    pub fn probe_ec_mark_merge_restore_p(n: usize) -> u64 {
        let (mut ec, ids) = fresh_p();
        let mut acc = 0u64;
        for round in 0..n / 16 {
            let t = ec.mark(prod::ShrinkPolicy::Never);
            for j in 0..16 {
                ec.merge(ids[(round + j * 5) % N], ids[(round + j * 11 + 1) % N]);
            }
            acc = acc.wrapping_add(ec.find(ids[round % N]).raw() as u64);
            ec.restore(t);
        }
        acc
    }

    pub fn run_all(n: usize) -> u64 {
        let mut acc = 0u64;
        acc = acc.wrapping_add(probe_ec_add_singleton_use_v(black_box(n)));
        acc = acc.wrapping_add(probe_ec_add_singleton_use_p(black_box(n)));
        acc = acc.wrapping_add(probe_ec_find_v(black_box(n)));
        acc = acc.wrapping_add(probe_ec_find_p(black_box(n)));
        acc = acc.wrapping_add(probe_ec_merge_v(black_box(n)));
        acc = acc.wrapping_add(probe_ec_merge_p(black_box(n)));
        acc = acc.wrapping_add(probe_ec_mark_merge_restore_v(black_box(n)));
        acc = acc.wrapping_add(probe_ec_mark_merge_restore_p(black_box(n)));
        acc
    }
}

// ---------------------------------------------------------------------------
// B+ tree set
// ---------------------------------------------------------------------------

macro_rules! bplus_probes {
    ($track:literal, $tag:ident) => {
        pub mod $tag {
            use super::*;
            type VT = verus::bplus::BPlusTreeSet<
                VId,
                verus::bplus_layout::Layout256,
                verus::bplus_search::BinarySearch,
                $track,
            >;
            type PT = prod::bplus::BPlusTreeSet<
                PId,
                prod::bplus::Layout256,
                prod::bplus::BinarySearch,
                $track,
            >;

            #[inline(never)]
            pub fn probe_bplus_insert_v(n: usize) -> u64 {
                let mut t = VT::new();
                let mut acc = 0u64;
                for k in 0..n as u32 {
                    if t.try_insert(VId::new((k * 2654435761u32) & 0x7FFF_FFFF))
                        .expect("ids")
                    {
                        acc = acc.wrapping_add(1);
                    }
                }
                acc
            }
            #[inline(never)]
            pub fn probe_bplus_insert_p(n: usize) -> u64 {
                let mut t = PT::new();
                let mut acc = 0u64;
                for k in 0..n as u32 {
                    if t.insert(PId::new((k * 2654435761u32) & 0x7FFF_FFFF)) {
                        acc = acc.wrapping_add(1);
                    }
                }
                acc
            }
            #[inline(never)]
            pub fn probe_bplus_contains_v(n: usize) -> u64 {
                let mut t = VT::new();
                for k in 0..N as u32 {
                    t.try_insert(VId::new(k * 3)).expect("ids");
                }
                let mut acc = 0u64;
                for k in 0..n as u32 {
                    if t.contains(VId::new((k * 7) % (3 * N as u32))) {
                        acc = acc.wrapping_add(1);
                    }
                }
                acc
            }
            #[inline(never)]
            pub fn probe_bplus_contains_p(n: usize) -> u64 {
                let mut t = PT::new();
                for k in 0..N as u32 {
                    t.insert(PId::new(k * 3));
                }
                let mut acc = 0u64;
                for k in 0..n as u32 {
                    let key = PId::new((k * 7) % (3 * N as u32));
                    let mut c = t.cursor();
                    c.seek(key);
                    if c.key() == Some(key) {
                        acc = acc.wrapping_add(1);
                    }
                }
                acc
            }

            pub fn run_all(n: usize) -> u64 {
                let mut acc = 0u64;
                acc = acc.wrapping_add(probe_bplus_insert_v(black_box(n)));
                acc = acc.wrapping_add(probe_bplus_insert_p(black_box(n)));
                acc = acc.wrapping_add(probe_bplus_contains_v(black_box(n)));
                acc = acc.wrapping_add(probe_bplus_contains_p(black_box(n)));
                acc
            }
        }
    };
}
bplus_probes!(false, bplus_untracked);
bplus_probes!(true, bplus_tracked);

// ---------------------------------------------------------------------------
// CircularList (verified only; the legacy ring lives in the e-classes layer)
// ---------------------------------------------------------------------------

macro_rules! ring_probes {
    ($track:literal, $tag:ident) => {
        pub mod $tag {
            use super::*;
            type VR = verus::CircularList<verus::Opt<VRingKey>, VRingNode, $track>;

            #[inline(never)]
            pub fn probe_ring_add_splice_v(n: usize) -> u64 {
                let mut r = VR::new();
                let first = r.try_add_singleton(verus::Opt::none()).expect("ids");
                let mut acc = 0u64;
                for _ in 0..n {
                    let x = r.try_add_singleton(verus::Opt::none()).expect("ids");
                    r.splice(first, x);
                    acc = acc.wrapping_add(x.raw() as u64);
                }
                acc
            }
            #[inline(never)]
            pub fn probe_ring_walk_v(n: usize) -> u64 {
                let mut r = VR::new();
                let first = r.try_add_singleton(verus::Opt::none()).expect("ids");
                for _ in 0..N {
                    let x = r.try_add_singleton(verus::Opt::none()).expect("ids");
                    r.splice(first, x);
                }
                let mut acc = 0u64;
                for _ in 0..n / N + 1 {
                    for x in r.iter_class(first) {
                        acc = acc.wrapping_add(x.raw() as u64);
                    }
                }
                acc
            }

            pub fn run_all(n: usize) -> u64 {
                let mut acc = 0u64;
                acc = acc.wrapping_add(probe_ring_add_splice_v(black_box(n)));
                acc = acc.wrapping_add(probe_ring_walk_v(black_box(n)));
                acc
            }
        }
    };
}
ring_probes!(false, ring_untracked);
ring_probes!(true, ring_tracked);

fn main() {
    let n = black_box(OPS);
    let mut acc = 0u64;
    acc = acc.wrapping_add(list_untracked::run_all(n));
    acc = acc.wrapping_add(list_tracked::run_all(n));
    acc = acc.wrapping_add(sparse_untracked::run_all(n));
    acc = acc.wrapping_add(sparse_tracked::run_all(n));
    acc = acc.wrapping_add(aov_untracked::run_all(n));
    acc = acc.wrapping_add(aov_tracked::run_all(n));
    acc = acc.wrapping_add(map_untracked::run_all(n));
    acc = acc.wrapping_add(map_tracked::run_all(n));
    acc = acc.wrapping_add(uf_untracked::run_all(n));
    acc = acc.wrapping_add(uf_tracked::run_all(n));
    acc = acc.wrapping_add(eclasses_tracked::run_all(n));
    acc = acc.wrapping_add(bplus_untracked::run_all(n));
    acc = acc.wrapping_add(bplus_tracked::run_all(n));
    acc = acc.wrapping_add(ring_untracked::run_all(n));
    acc = acc.wrapping_add(ring_tracked::run_all(n));
    println!("composite probe checksum {acc}");
}

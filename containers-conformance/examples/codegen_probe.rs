// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Codegen probe: one `#[inline(never)]` function per (container, store, mode,
//! method), each running the method in a tight loop, so every method gets its
//! own symbol whose machine code can be audited (inlining failures, values
//! carried through the stack across iterations, panic paths, loop size).
//! It is not a benchmark: it exists to be disassembled.
//!
//! Build: `cargo build --release -p containers-conformance --example codegen_probe`
//! then run `tools/codegen_audit.py target/release/examples/codegen_probe`.
#![allow(clippy::all)]

use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::hint::black_box;
use verus::dyn_store::StoreKind;
use verus::group::ForkHistory;
use verus::tier_policy::TierPolicy;
use verus::vec::ShrinkPolicy;

verus::define_id31! { pub struct VElem / StoredVElem, "e"; }
verus::define_id31! { pub struct VList / StoredVList, "l"; }
verus::define_id31! { pub struct VNode / StoredVNode, "n"; }

const N: usize = 4096;
const OPS: usize = 8192;

// ---------------------------------------------------------------------------
// Vec (VecD: one enum, one dispatch per op) for every store kind and mode.
// ---------------------------------------------------------------------------

macro_rules! vec_probes {
    ($kind:ident, $track:literal, $tag:ident) => {
        pub mod $tag {
            use super::*;
            type V = verus::VecD<u64, u32, $track>;

            fn fresh() -> V {
                let mut v = V::new_kind_with_policy(StoreKind::$kind, TierPolicy::default());
                for i in 0..N as u64 {
                    v.try_push(i).expect("capacity");
                }
                v
            }

            #[inline(never)]
            pub fn probe_vec_push(n: usize) -> u64 {
                let mut v = V::new_kind_with_policy(StoreKind::$kind, TierPolicy::default());
                for i in 0..n as u64 {
                    v.try_push(i).expect("capacity");
                }
                v.len() as u64
            }

            #[inline(never)]
            pub fn probe_vec_pop(n: usize) -> u64 {
                let mut v = fresh();
                let mut acc = 0u64;
                for _ in 0..n {
                    if let Some(x) = v.pop() {
                        acc = acc.wrapping_add(x);
                    }
                }
                acc
            }

            #[inline(never)]
            pub fn probe_vec_set_index(n: usize) -> u64 {
                let mut v = fresh();
                for k in 0..n {
                    v.set_index(((k * 7) % N) as u32, k as u64);
                }
                v.len() as u64
            }

            #[inline(never)]
            pub fn probe_vec_get_index(n: usize) -> u64 {
                let v = fresh();
                let mut acc = 0u64;
                for k in 0..n {
                    acc = acc.wrapping_add(v.get_index(((k * 7) % N) as u32));
                }
                acc
            }

            #[inline(never)]
            pub fn probe_vec_get_set(n: usize) -> u64 {
                let mut v = fresh();
                let mut acc = 0u64;
                for k in 0..n {
                    let i = ((k * 7) % N) as u32;
                    acc = acc.wrapping_add(v.get(i));
                    v.set(i, acc);
                }
                acc
            }

            #[inline(never)]
            pub fn probe_vec_as_slice_sum(n: usize) -> u64 {
                let v = fresh();
                let mut acc = 0u64;
                for _ in 0..n / N + 1 {
                    if let Some(s) = v.as_slice() {
                        for x in s {
                            acc = acc.wrapping_add(*x);
                        }
                    }
                }
                acc
            }

            #[inline(never)]
            pub fn probe_vec_try_extend(n: usize) -> u64 {
                let mut v = V::new_kind_with_policy(StoreKind::$kind, TierPolicy::default());
                let chunk = [1u64, 2, 3, 4, 5, 6, 7, 8];
                for _ in 0..n / 8 {
                    v.try_extend(&chunk).expect("capacity");
                }
                v.len() as u64
            }

            #[inline(never)]
            pub fn probe_vec_push_untracked(n: usize) -> u64 {
                let mut v = V::new_kind_with_policy(StoreKind::$kind, TierPolicy::default());
                for i in 0..n as u64 {
                    v.push_untracked(i);
                }
                v.len() as u64
            }

            #[inline(never)]
            pub fn probe_vec_set_untracked(n: usize) -> u64 {
                let mut v = fresh();
                for k in 0..n {
                    v.set_untracked(((k * 7) % N) as u32, k as u64);
                }
                v.len() as u64
            }

            #[inline(never)]
            pub fn probe_vec_mark_set_restore(n: usize) -> u64 {
                let mut v = ForkHistory::new(fresh());
                let mut acc = 0u64;
                for round in 0..n / 64 {
                    let t = v.mark(ShrinkPolicy::Never).expect("mark");
                    for k in 0..64 {
                        v.set_index(((round * 64 + k * 5) % N) as u32, k as u64);
                    }
                    acc = acc.wrapping_add(v.get_index(0));
                    assert!(v.restore(t));
                    assert!(v.pop_scope());
                }
                acc
            }

            #[inline(never)]
            pub fn probe_vec_mark_push_restore_and_pop(n: usize) -> u64 {
                let mut v = ForkHistory::new(fresh());
                let mut acc = 0u64;
                for round in 0..n / 64 {
                    let t = v.mark(ShrinkPolicy::Never).expect("mark");
                    for k in 0..64u64 {
                        v.try_push(k + round as u64).expect("capacity");
                    }
                    acc = acc.wrapping_add(v.len() as u64);
                    assert!(v.restore_and_pop(t));
                }
                acc
            }

            #[inline(never)]
            pub fn probe_vec_mark_pop_scope(n: usize) -> u64 {
                let mut v = ForkHistory::new(fresh());
                let mut acc = 0u64;
                for _ in 0..n / 8 {
                    let _t = v.mark(ShrinkPolicy::Never).expect("mark");
                    v.set_index(3, acc);
                    acc = acc.wrapping_add(v.get_index(3));
                    assert!(v.pop_scope());
                }
                acc
            }

            #[inline(never)]
            pub fn probe_vec_nested_marks(n: usize) -> u64 {
                let mut v = ForkHistory::new(fresh());
                let mut acc = 0u64;
                for round in 0..n / 256 {
                    let outer = v.mark(ShrinkPolicy::Never).expect("mark");
                    for d in 0..8 {
                        let inner = v.mark(ShrinkPolicy::Never).expect("mark");
                        for k in 0..16 {
                            v.set_index(((round + d * 16 + k) % N) as u32, k as u64);
                        }
                        acc = acc.wrapping_add(v.get_index((d % N) as u32));
                        assert!(v.restore_and_pop(inner));
                    }
                    assert!(v.restore_and_pop(outer));
                }
                acc
            }

            pub fn run_all(n: usize) -> u64 {
                let mut acc = 0u64;
                acc = acc.wrapping_add(probe_vec_push(black_box(n)));
                acc = acc.wrapping_add(probe_vec_pop(black_box(n)));
                acc = acc.wrapping_add(probe_vec_set_index(black_box(n)));
                acc = acc.wrapping_add(probe_vec_get_index(black_box(n)));
                acc = acc.wrapping_add(probe_vec_get_set(black_box(n)));
                acc = acc.wrapping_add(probe_vec_as_slice_sum(black_box(n)));
                acc = acc.wrapping_add(probe_vec_try_extend(black_box(n)));
                acc = acc.wrapping_add(probe_vec_push_untracked(black_box(n)));
                acc = acc.wrapping_add(probe_vec_set_untracked(black_box(n)));
                if $track {
                    acc = acc.wrapping_add(probe_vec_mark_set_restore(black_box(n)));
                    acc = acc.wrapping_add(probe_vec_mark_push_restore_and_pop(black_box(n)));
                    acc = acc.wrapping_add(probe_vec_mark_pop_scope(black_box(n)));
                    acc = acc.wrapping_add(probe_vec_nested_marks(black_box(n)));
                }
                acc
            }
        }
    };
}

vec_probes!(Inline, false, vec_inline_untracked);
vec_probes!(Parallel, false, vec_parallel_untracked);
vec_probes!(Trail, false, vec_trail_untracked);
vec_probes!(Inline, true, vec_inline_tracked);
vec_probes!(Parallel, true, vec_parallel_tracked);
vec_probes!(Trail, true, vec_trail_tracked);

// ---------------------------------------------------------------------------
// Static Vec (no enum): the two stores that expose `new` directly, both modes.
// ---------------------------------------------------------------------------

macro_rules! static_vec_probes {
    ($store:ty, $track:literal, $tag:ident) => {
        pub mod $tag {
            use super::*;
            type V = verus::vec::Vec<u64, u32, $store, $track>;

            fn fresh() -> V {
                let mut v = V::new();
                for i in 0..N as u64 {
                    v.try_push(i).expect("capacity");
                }
                v
            }

            #[inline(never)]
            pub fn probe_svec_push(n: usize) -> u64 {
                let mut v = V::new();
                for i in 0..n as u64 {
                    v.try_push(i).expect("capacity");
                }
                v.len() as u64
            }

            #[inline(never)]
            pub fn probe_svec_set_index(n: usize) -> u64 {
                let mut v = fresh();
                for k in 0..n {
                    v.set_index(((k * 7) % N) as u32, k as u64);
                }
                v.len() as u64
            }

            /// Diagnostic twin of `probe_svec_set_index`: the container is never
            /// dropped, so the loop carries no unwind landing pad for it.
            #[inline(never)]
            pub fn probe_svec_set_index_nodrop(n: usize) -> u64 {
                let mut v = std::mem::ManuallyDrop::new(fresh());
                for k in 0..n {
                    v.set_index(((k * 7) % N) as u32, k as u64);
                }
                v.len() as u64
            }

            #[inline(never)]
            pub fn probe_svec_get_index(n: usize) -> u64 {
                let v = fresh();
                let mut acc = 0u64;
                for k in 0..n {
                    acc = acc.wrapping_add(v.get_index(((k * 7) % N) as u32));
                }
                acc
            }

            #[inline(never)]
            pub fn probe_svec_pop(n: usize) -> u64 {
                let mut v = fresh();
                let mut acc = 0u64;
                for _ in 0..n {
                    if let Some(x) = v.pop() {
                        acc = acc.wrapping_add(x);
                    }
                }
                acc
            }

            #[inline(never)]
            pub fn probe_svec_mark_set_restore(n: usize) -> u64 {
                let mut v = ForkHistory::new(fresh());
                let mut acc = 0u64;
                for round in 0..n / 64 {
                    let t = v.mark(ShrinkPolicy::Never).expect("mark");
                    for k in 0..64 {
                        v.set_index(((round * 64 + k * 5) % N) as u32, k as u64);
                    }
                    acc = acc.wrapping_add(v.get_index(0));
                    assert!(v.restore_and_pop(t));
                }
                acc
            }

            pub fn run_all(n: usize) -> u64 {
                let mut acc = 0u64;
                acc = acc.wrapping_add(probe_svec_push(black_box(n)));
                acc = acc.wrapping_add(probe_svec_set_index(black_box(n)));
                acc = acc.wrapping_add(probe_svec_set_index_nodrop(black_box(n)));
                acc = acc.wrapping_add(probe_svec_get_index(black_box(n)));
                acc = acc.wrapping_add(probe_svec_pop(black_box(n)));
                if $track {
                    acc = acc.wrapping_add(probe_svec_mark_set_restore(black_box(n)));
                }
                acc
            }
        }
    };
}

static_vec_probes!(verus::inline_store::InlineStore<u64, u32>, false, svec_inline_untracked);
static_vec_probes!(verus::parallel_store::ParallelStore<u64, u32>, false, svec_parallel_untracked);
static_vec_probes!(verus::inline_store::InlineStore<u64, u32>, true, svec_inline_tracked);
static_vec_probes!(verus::parallel_store::ParallelStore<u64, u32>, true, svec_parallel_tracked);

// ---------------------------------------------------------------------------
// Legacy (production) Vec counterparts: the like-for-like baseline per method.
// ---------------------------------------------------------------------------

macro_rules! legacy_vec_probes {
    ($vt:ident, $track:literal, $tag:ident) => {
        pub mod $tag {
            use super::*;
            type V = prod::$vt<u64, u32, $track>;

            fn fresh() -> V {
                let mut v = V::new();
                for i in 0..N as u64 {
                    v.push(i);
                }
                v
            }

            #[inline(never)]
            pub fn probe_lvec_push(n: usize) -> u64 {
                let mut v = V::new();
                for i in 0..n as u64 {
                    v.push(i);
                }
                v.len() as u64
            }

            #[inline(never)]
            pub fn probe_lvec_pop(n: usize) -> u64 {
                let mut v = fresh();
                let mut acc = 0u64;
                for _ in 0..n {
                    if let Some(x) = v.pop() {
                        acc = acc.wrapping_add(x);
                    }
                }
                acc
            }

            #[inline(never)]
            pub fn probe_lvec_set(n: usize) -> u64 {
                let mut v = fresh();
                for k in 0..n {
                    v.set(((k * 7) % N) as u32, k as u64);
                }
                v.len() as u64
            }

            #[inline(never)]
            pub fn probe_lvec_get(n: usize) -> u64 {
                let v = fresh();
                let mut acc = 0u64;
                for k in 0..n {
                    acc = acc.wrapping_add(v.get(((k * 7) % N) as u32));
                }
                acc
            }

            #[inline(never)]
            pub fn probe_lvec_get_set(n: usize) -> u64 {
                let mut v = fresh();
                let mut acc = 0u64;
                for k in 0..n {
                    let i = ((k * 7) % N) as u32;
                    acc = acc.wrapping_add(v.get(i));
                    v.set(i, acc);
                }
                acc
            }

            #[inline(never)]
            pub fn probe_lvec_mark_set_restore(n: usize) -> u64 {
                let mut v = fresh();
                let mut acc = 0u64;
                for round in 0..n / 64 {
                    let t = v.mark(prod::ShrinkPolicy::Never);
                    for k in 0..64 {
                        v.set(((round * 64 + k * 5) % N) as u32, k as u64);
                    }
                    acc = acc.wrapping_add(v.get(0u32));
                    v.restore(t);
                }
                acc
            }

            pub fn run_all(n: usize) -> u64 {
                let mut acc = 0u64;
                acc = acc.wrapping_add(probe_lvec_push(black_box(n)));
                acc = acc.wrapping_add(probe_lvec_pop(black_box(n)));
                acc = acc.wrapping_add(probe_lvec_set(black_box(n)));
                acc = acc.wrapping_add(probe_lvec_get(black_box(n)));
                acc = acc.wrapping_add(probe_lvec_get_set(black_box(n)));
                if $track {
                    acc = acc.wrapping_add(probe_lvec_mark_set_restore(black_box(n)));
                }
                acc
            }
        }
    };
}

legacy_vec_probes!(VecI, false, lvec_inline_untracked);
legacy_vec_probes!(VecP, false, lvec_parallel_untracked);
legacy_vec_probes!(VecI, true, lvec_inline_tracked);
legacy_vec_probes!(VecP, true, lvec_parallel_tracked);

fn main() {
    let n = black_box(OPS);
    let mut acc = 0u64;
    acc = acc.wrapping_add(vec_inline_untracked::run_all(n));
    acc = acc.wrapping_add(vec_parallel_untracked::run_all(n));
    acc = acc.wrapping_add(vec_trail_untracked::run_all(n));
    acc = acc.wrapping_add(vec_inline_tracked::run_all(n));
    acc = acc.wrapping_add(vec_parallel_tracked::run_all(n));
    acc = acc.wrapping_add(vec_trail_tracked::run_all(n));
    acc = acc.wrapping_add(svec_inline_untracked::run_all(n));
    acc = acc.wrapping_add(svec_parallel_untracked::run_all(n));
    acc = acc.wrapping_add(svec_inline_tracked::run_all(n));
    acc = acc.wrapping_add(svec_parallel_tracked::run_all(n));
    acc = acc.wrapping_add(lvec_inline_untracked::run_all(n));
    acc = acc.wrapping_add(lvec_parallel_untracked::run_all(n));
    acc = acc.wrapping_add(lvec_inline_tracked::run_all(n));
    acc = acc.wrapping_add(lvec_parallel_tracked::run_all(n));
    println!("codegen probe checksum {acc}");
}

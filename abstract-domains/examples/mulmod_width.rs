// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Measures `Word::mulmod` against a same-width double-and-add loop, the
//! alternative to a widening product. Run with
//! `cargo run --release --example mulmod_width -p semi-persistent-abstract-domains`.
use semi_persistent_abstract_domains::word::Word;
use std::hint::black_box;
use std::time::Instant;

macro_rules! same_width {
    ($name:ident, $t:ty) => {
        /// (a * b) mod m with every intermediate value below m.
        fn $name(a: $t, b: $t, m: $t) -> $t {
            let add = |x: $t, y: $t| if x >= m - y { x - (m - y) } else { x + y };
            let (mut r, mut base, mut e) = (0, a % m, b);
            while e > 0 {
                if e & 1 == 1 {
                    r = add(r, base);
                }
                base = add(base, base);
                e >>= 1;
            }
            r
        }
    };
}
same_width!(loop_u64, u64);
same_width!(loop_u32, u32);

fn xorshift(s: &mut u64) -> u64 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    *s
}

fn time<T, F>(v: &[(T, T, T)], f: F) -> f64
where
    T: Copy + std::ops::Add<Output = T> + Default,
    F: Fn(T, T, T) -> T,
{
    let t = Instant::now();
    let mut acc = T::default();
    for &(a, b, m) in v {
        acc = acc + f(black_box(a), black_box(b), black_box(m));
    }
    black_box(acc);
    t.elapsed().as_nanos() as f64 / v.len() as f64
}

fn main() {
    let n = 2_000_000;
    for (label, mask) in [
        ("u64 full range", u64::MAX),
        ("u64 operands < 2^32", 0xffff_ffff),
    ] {
        let mut s = 0x9e37_79b9_7f4a_7c15;
        let v: Vec<(u64, u64, u64)> = (0..n)
            .map(|_| {
                (
                    xorshift(&mut s) & mask,
                    xorshift(&mut s) & mask,
                    (xorshift(&mut s) >> 1).max(1),
                )
            })
            .collect();
        let w = time(&v, <u64 as Word>::mulmod);
        let l = time(&v, loop_u64);
        println!("{label:22} Word::mulmod {w:6.1} ns   same-width loop {l:6.1} ns");
    }
    let mut s = 0x9e37_79b9_7f4a_7c15;
    let v: Vec<(u32, u32, u32)> = (0..n)
        .map(|_| {
            (
                xorshift(&mut s) as u32,
                xorshift(&mut s) as u32,
                (xorshift(&mut s) as u32 >> 1).max(1),
            )
        })
        .collect();
    let w = time(&v, <u32 as Word>::mulmod);
    let l = time(&v, loop_u32);
    println!(
        "{:22} Word::mulmod {w:6.1} ns   same-width loop {l:6.1} ns",
        "u32 full range"
    );
}

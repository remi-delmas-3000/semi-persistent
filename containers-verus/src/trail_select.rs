// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Physical first-capture selection for chronological Trail frames.
use vstd::prelude::*;

verus! {
use crate::index_like::IndexLike;

pub(crate) open spec fn has_position(keys: Seq<(usize, usize)>, p: int) -> bool {
    exists|q: int| 0 <= q < keys.len() && (#[trigger] keys[q]).1 == p
}

/// Each key identifies an actual source position, and every source position
/// occurs. This relation survives a permutation of the key buffer.
pub(crate) open spec fn keyed_source<T, I: IndexLike>(entries: Seq<(T, I)>, keys: Seq<(usize, usize)>) -> bool {
    &&& keys.len() == entries.len()
    &&& forall|q: int| 0 <= q < keys.len() ==> {
        &&& (#[trigger] keys[q]).1 < entries.len()
        &&& keys[q].0 as nat == entries[keys[q].1 as int].1.as_nat()
    }
    &&& forall|p: int| 0 <= p < entries.len() ==>
        #[trigger] has_position(keys, p)
}

pub(crate) open spec fn keys_sorted(keys: Seq<(usize, usize)>) -> bool {
    forall|a: int, b: int| 0 <= a < b < keys.len() ==>
        (#[trigger] keys[a]).0 < (#[trigger] keys[b]).0
        || (keys[a].0 == keys[b].0 && keys[a].1 <= keys[b].1)
}

#[verifier::spinoff_prover]
pub(crate) fn build_keys<T: Copy, I: IndexLike>(
    entries: &[(T, I)], keys: &mut std::vec::Vec<(usize, usize)>,
)
    ensures final(keys)@.len() == entries@.len(),
        forall|q: int| 0 <= q < entries@.len() ==> {
            &&& (#[trigger] final(keys)@[q]).0 as nat == entries@[q].1.as_nat()
            &&& final(keys)@[q].1 == q
        },
        keyed_source::<T, I>(entries@, final(keys)@),
{
    keys.clear();
    let n = entries.len();
    keys.reserve(n);
    let mut q = 0usize;
    while q < n
        invariant q <= n == entries@.len(), keys@.len() == q,
            forall|p: int| 0 <= p < q ==> {
                &&& (#[trigger] keys@[p]).0 as nat == entries@[p].1.as_nat()
                &&& keys@[p].1 == p
            },
        decreases n - q,
    {
        let index = entries[q].1.as_usize();
        keys.push((index, q));
        q += 1;
    }
    proof {
        assert forall|p: int| 0 <= p < entries@.len() implies
            #[trigger] has_position(keys@, p) by {
            assert(keys@[p].1 == p);
        }
    }
}

/// Lexicographic ordering places the least chronological position first in
/// every index group; duplicate later writes cannot replace that saved value.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_group_first<T, I: IndexLike>(
    entries: Seq<(T, I)>, keys: Seq<(usize, usize)>, q: int,
)
    requires keyed_source::<T, I>(entries, keys), keys_sorted(keys),
        0 <= q < keys.len(), q == 0 || keys[q - 1].0 != keys[q].0,
    ensures keys[q].1 < entries.len(),
        entries[keys[q].1 as int].1.as_nat() == keys[q].0 as nat,
        crate::vec::first_hitter::<T, I>(entries, 0, keys[q].1 as int, keys[q].0 as nat),
{
    assert forall|p: int| 0 <= p < keys[q].1 implies
        (#[trigger] entries[p]).1.as_nat() != keys[q].0 as nat by {
        if entries[p].1.as_nat() == keys[q].0 as nat {
            assert(has_position(keys, p));
            let r = choose|r: int| 0 <= r < keys.len() && (#[trigger] keys[r]).1 == p;
            assert(keys[r].0 == keys[q].0);
            if r > q { assert(keys[q].1 <= keys[r].1); }
            assert(r < q);
            assert(q > 0);
            if r < q - 1 { assert(keys[r].0 <= keys[q - 1].0); }
            assert(keys[q - 1].0 <= keys[q].0);
            assert(keys[q - 1].0 == keys[q].0);
        }
    }
}
/// Positions retained by the production scan of the first `n` sorted keys.
pub(crate) open spec fn group_positions(keys: Seq<(usize, usize)>, n: int) -> Seq<usize>
    recommends 0 <= n <= keys.len(),
    decreases n,
{
    if n <= 0 { Seq::empty() }
    else if n == 1 || keys[n - 2].0 != keys[n - 1].0 {
        group_positions(keys, n - 1).push(keys[n - 1].1)
    } else { group_positions(keys, n - 1) }
}

/// The same linear group scan used by ordinary Trail migration, with an exact
/// result contract. Sorting and source correspondence are separate obligations.
#[verifier::spinoff_prover]
pub(crate) fn select_positions(keys: &[(usize, usize)], selected: &mut std::vec::Vec<usize>)
    ensures final(selected)@ == group_positions(keys@, keys@.len() as int),
{
    selected.clear();
    let mut previous: Option<usize> = None;
    let mut q = 0usize;
    while q < keys.len()
        invariant q <= keys@.len(),
            selected@ == group_positions(keys@, q as int),
            previous == (if q == 0 { None } else { Some(keys@[q as int - 1].0) }),
        decreases keys@.len() - q,
    {
        let (index, position) = keys[q];
        if previous != Some(index) {
            selected.push(position);
            previous = Some(index);
        }
        q += 1;
    }
}

/// Every retained position is a group head, hence the source's earliest capture.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_selected_first<T, I: IndexLike>(
    entries: Seq<(T, I)>, keys: Seq<(usize, usize)>, n: int,
)
    requires keyed_source::<T, I>(entries, keys), keys_sorted(keys), 0 <= n <= keys.len(),
    ensures forall|p: usize| #[trigger] group_positions(keys, n).contains(p) ==> {
        &&& p < entries.len()
        &&& crate::vec::first_hitter::<T, I>(entries, 0, p as int, entries[p as int].1.as_nat())
    },
    decreases n,
{
    if n > 0 {
        lemma_selected_first::<T, I>(entries, keys, n - 1);
        if n == 1 || keys[n - 2].0 != keys[n - 1].0 {
            lemma_group_first::<T, I>(entries, keys, n - 1);
        }
    }
    assert forall|p: usize| #[trigger] group_positions(keys, n).contains(p) implies {
        &&& p < entries.len()
        &&& crate::vec::first_hitter::<T, I>(entries, 0, p as int, entries[p as int].1.as_nat())
    } by {
        if n > 0 {
            if (n == 1 || keys[n - 2].0 != keys[n - 1].0) && p == keys[n - 1].1 {
            } else {
                assert(group_positions(keys, n - 1).contains(p));
            }
        }
    }
}
/// Sorting must supply multiset equality; no sorting contract is assumed here.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_keyed_permutation<T, I: IndexLike>(
    entries: Seq<(T, I)>, before: Seq<(usize, usize)>, after: Seq<(usize, usize)>,
)
    requires keyed_source::<T, I>(entries, before), before.to_multiset() == after.to_multiset(),
    ensures keyed_source::<T, I>(entries, after),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    vstd::seq_lib::to_multiset_len(before);
    vstd::seq_lib::to_multiset_len(after);
    assert(before.len() == after.len());
    assert forall|q: int| 0 <= q < after.len() implies {
        &&& (#[trigger] after[q]).1 < entries.len()
        &&& after[q].0 as nat == entries[after[q].1 as int].1.as_nat()
    } by {
        assert(after.contains(after[q]));
        vstd::seq_lib::to_multiset_contains(after, after[q]);
        vstd::seq_lib::to_multiset_contains(before, after[q]);
        let r = choose|r: int| 0 <= r < before.len() && before[r] == after[q];
    }
    assert forall|p: int| 0 <= p < entries.len() implies
        #[trigger] has_position(after, p) by {
        assert(has_position(before, p));
        let r = choose|r: int| 0 <= r < before.len() && (#[trigger] before[r]).1 == p;
        assert(before.contains(before[r]));
        vstd::seq_lib::to_multiset_contains(before, before[r]);
        vstd::seq_lib::to_multiset_contains(after, before[r]);
        let q = choose|q: int| 0 <= q < after.len() && after[q] == before[r];
        assert(after[q].1 == p);
    }
}
/// Every input key's index has a retained group head, including duplicate runs.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_selected_covers(keys: Seq<(usize, usize)>, n: int, q: int)
    requires 0 <= q < n <= keys.len(),
    ensures exists|r: int| 0 <= r < n && (#[trigger] keys[r]).0 == keys[q].0
        && group_positions(keys, n).contains(keys[r].1)
        && (r == 0 || keys[r - 1].0 != keys[r].0),
    decreases n,
{
    broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
    if q < n - 1 {
        lemma_selected_covers(keys, n - 1, q);
        let r = choose|r: int| 0 <= r < n - 1 && keys[r].0 == keys[q].0
            && group_positions(keys, n - 1).contains(keys[r].1)
            && (r == 0 || keys[r - 1].0 != keys[r].0);
        assert(group_positions(keys, n).contains(keys[r].1));
    } else if n == 1 || keys[n - 2].0 != keys[n - 1].0 {
        assert(group_positions(keys, n).contains(keys[q].1));
    } else {
        lemma_selected_covers(keys, n - 1, n - 2);
        let r = choose|r: int| 0 <= r < n - 1 && keys[r].0 == keys[n - 2].0
            && group_positions(keys, n - 1).contains(keys[r].1)
            && (r == 0 || keys[r - 1].0 != keys[r].0);
        assert(group_positions(keys, n).contains(keys[r].1));
    }
}
} // verus!

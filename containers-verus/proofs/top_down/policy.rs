// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Conditional preservation by eligible oldest-prefix migration plans. Policy
//! cost and threshold accuracy is separate from this semantic theorem.

use super::mutation::*;
use super::*;

verus! {

pub enum Source { Trail, Hot }
pub enum Policy { Configured, ForceTrail, ForceHot, Adaptive, Defer }
pub struct Plan<T> {
    pub source: Source,
    pub count: nat,
    pub frames: Seq<Frame<T>>,
}

pub open spec fn eligible<T, R: View<T>>(s: R, source: Source) -> int {
    match source {
        Source::Trail => if s.trail() > 0 { s.trail() - 1 } else { 0 },
        Source::Hot => if s.unique() && s.hot() > 0 { s.hot() - 1 } else { s.hot() },
    }
}

/// A precomputed plan must name exactly the selected source frames, not just
/// fit a count bound. Empty frame meanings remain in this sequence.
pub open spec fn plan_ok<T, R: View<T>>(s: R, p: Plan<T>) -> bool {
    let offset = if p.source is Trail { s.cold() + s.hot() } else { s.cold() };
    p.count <= eligible(s, p.source)
        && p.frames == s.model().frames.subrange(offset, offset + p.count)
}

pub trait Policies<T>: Mutations<T> {
    /// Thresholds choose a count; the semantic contract requires the complete
    /// source frame meanings and excludes the active writable frame.
    proof fn select_plan(pre: Self, policy: Policy, source: Source) -> (plan: Plan<T>)
        requires stable(pre),
        ensures plan_ok(pre, plan), plan.source == source,
            policy is Defer ==> plan.count == 0,
            policy is ForceTrail ==> if source is Trail {
                plan.count == eligible(pre, source)
            } else { plan.count == 0 },
            policy is ForceHot ==> if source is Hot {
                plan.count == eligible(pre, source)
            } else { plan.count == 0 };

    /// Completed migration composes local transform, append, retirement, and
    /// rebasing. It exports exact map equality and physical frame-count effects.
    proof fn migrate(pre: Self, plan: Plan<T>) -> (out: Self)
        requires stable(pre), plan_ok(pre, plan),
        ensures physical(out), writable(out), capture_ok(out), same_protocol(out, pre),
            out.model() == pre.model(), out.canonical() == pre.canonical(),
            if plan.source is Trail {
                out.cold() == pre.cold() && out.hot() == pre.hot() + plan.count
                    && out.trail() == pre.trail() - plan.count
            } else {
                out.cold() == pre.cold() + plan.count && out.hot() == pre.hot() - plan.count
                    && out.trail() == pre.trail()
            };

    /// Preserve the existing mark token coordinate contract. Token validity
    /// is still tested by the independent public restore predicate.
    proof fn make_token(pre: Self, coordinate: int) -> (token: Self::Token)
        requires stable(pre), 0 <= coordinate < pre.model().frames.len(),
        ensures Self::coordinate(token) == coordinate;
}

#[verifier::spinoff_prover]
pub proof fn apply_policy<T, R: Policies<T>>(pre: R, policy: Policy) -> (out: R)
    requires stable(pre),
    ensures stable(out), out.model() == pre.model(), same_protocol(out, pre),
        out.canonical() == pre.canonical(),
{
    let trail_plan = R::select_plan(pre, policy, Source::Trail);
    let after_trail = R::migrate(pre, trail_plan);
    let hot_plan = R::select_plan(after_trail, policy, Source::Hot);
    R::migrate(after_trail, hot_plan)
}

#[verifier::spinoff_prover]
pub proof fn mark_public<T, R: Policies<T>>(pre: R, policy: Policy) -> (result: (R, R::Token))
    requires stable(pre), pre.can_mark(),
    ensures stable(result.0), result.0.model() == mark(pre.model()), same_protocol(result.0, pre),
        R::coordinate(result.1) == pre.model().frames.len(),
{
    let opened = mark_core(pre);
    let out = apply_policy(opened, policy);
    let token = R::make_token(out, pre.model().frames.len() as int);
    (out, token)
}

/// Every rejected request preserves the state, not merely its current values.
/// The concrete adapter must additionally retain its existing error variants.
#[verifier::spinoff_prover]
pub proof fn try_mark_public<T, R: Policies<T>>(pre: R, policy: Policy) -> (result: (R, Option<R::Token>))
    requires stable(pre),
    ensures stable(result.0),
        result.1 is Some ==> result.0.model() == mark(pre.model())
            && R::coordinate(result.1->Some_0) == pre.model().frames.len(),
        result.1 is None ==> result.0 == pre,
{
    if pre.can_mark() {
        let (out, token) = mark_public(pre, policy);
        (out, Some(token))
    } else { (pre, None) }
}

} // verus!

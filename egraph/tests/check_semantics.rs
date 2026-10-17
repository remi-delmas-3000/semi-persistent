// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `check` and `prove` (doc/goal-egglog-check.md).
//!
//! `prove` is the build-and-compare check: it builds its terms, rebuilds, and compares
//! classes. These tests fix that meaning before `check` moves to egglog's query semantics.

use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{BignumLit, BignumModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::parser::parse_program_v2;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::sortcheck::sortcheck_program;

type Interp = Interpreter<DefaultConfig, BignumLit, BignumModel, true, false>;

fn run(src: &str) -> Result<Interp, String> {
    let surface = parse_program_v2(src).map_err(|e| e.to_string())?;
    let mut interp = Interp::new(BignumModel);
    let mut globals = GlobalCtx::new();
    let checked = sortcheck_program(surface, &mut interp.eg, &interp.model, &mut globals)
        .map_err(|e| e.to_string())?;
    interp.run_checked(&checked).map_err(|e| e.to_string())?;
    Ok(interp)
}

const DECLS: &str = "
(sort E)
(function f (E) E)
(function a () E)
(function b () E)
(function c () E)
(union (a) (b))
";

#[test]
fn prove_builds_terms_and_closes_under_congruence() {
    // Neither `(f (a))` nor `(f (b))` exists before the command; `prove` builds both, and
    // congruence joins them because `(a)` and `(b)` are one class.
    run(&format!("{DECLS}(prove (= (f (a)) (f (b))))")).expect("equal by congruence");
    run(&format!("{DECLS}(prove (!= (f (a)) (f (c))))")).expect("distinct");
}

#[test]
fn prove_fails_on_the_wrong_relation() {
    let e = run(&format!("{DECLS}(prove (= (f (a)) (f (c))))"))
        .err()
        .expect("not equal");
    assert!(e.contains("terms are not equal"), "{e}");
    let e = run(&format!("{DECLS}(prove (!= (a) (b)))"))
        .err()
        .expect("equal");
    assert!(e.contains("terms are equal"), "{e}");
}

#[test]
fn prove_of_one_term_builds_it() {
    let interp = run(&format!("{DECLS}(prove (f (c)))")).expect("builds");
    assert!(interp.eg.node_count() >= 4, "the term was built");
}

const UNBOUNDED: &str = "
(sort N)
(constructor z () N)
(constructor s (N) N)
(rewrite (s x) (s (s x)))
(let start (s (z)))
";

#[test]
fn goal_stops_the_run_as_until_does() {
    let until = run(&format!(
        "{UNBOUNDED}(run 100 :until (= start (s (s (z)))))"
    ))
    .unwrap();
    let goal = run(&format!("{UNBOUNDED}(run 100 :goal (= start (s (s (z)))))")).unwrap();
    let (u, g) = (until.last_sat().unwrap(), goal.last_sat().unwrap());
    assert!(u.goal_met && g.goal_met);
    assert_eq!(u.iterations, g.iterations);
}

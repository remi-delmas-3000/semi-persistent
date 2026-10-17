// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `check` and `prove` (doc/goal-egglog-check.md).
//!
//! `prove` is the build-and-compare check: it builds its terms, rebuilds, and compares
//! classes. `check` is egglog's: a conjunctive query over the current e-graph that
//! succeeds when it has a match, and builds nothing.

use semi_persistent_egraph::interpret::{AcMode, Interpreter};
use semi_persistent_egraph::model::{BignumLit, BignumModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::parser::parse_program_v2;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::sortcheck::sortcheck_program;

type Interp = Interpreter<DefaultConfig, BignumLit, BignumModel, true, false>;

fn run(src: &str) -> Result<Interp, String> {
    run_in(src, AcMode::Off)
}

fn run_in(src: &str, mode: AcMode) -> Result<Interp, String> {
    let surface = parse_program_v2(src).map_err(|e| e.to_string())?;
    let mut interp = Interp::new(BignumModel);
    interp.set_ac_mode(mode);
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

// ── `check`: egglog's query ─────────────────────────────────────────────────

#[test]
fn check_compares_terms_that_exist() {
    run(&format!(
        "{DECLS}(let x (f (a)))\n(let y (f (b)))\n(check (= x y))"
    ))
    .unwrap();
    run(&format!(
        "{DECLS}(let x (f (a)))\n(let y (f (b)))\n(check (= (f (a)) (f (b))))"
    ))
    .unwrap();
    let e = run(&format!(
        "{DECLS}(let x (f (a)))\n(let y (f (c)))\n(check (= x y))"
    ))
    .err()
    .expect("different classes");
    assert!(e.contains("no match for (= x y)"), "{e}");
}

#[test]
fn check_does_not_build_its_terms() {
    // `prove` builds `(f (a))` and `(f (b))` and joins them by congruence; `check` looks
    // them up, finds neither, and fails, as egglog's does.
    run(&format!("{DECLS}(prove (= (f (a)) (f (b))))")).unwrap();
    let e = run(&format!("{DECLS}(check (= (f (a)) (f (b))))"))
        .err()
        .expect("not built");
    assert!(e.contains("no match"), "{e}");
    let e = run(&format!("{DECLS}(check (f (c)))"))
        .err()
        .expect("not built");
    assert!(e.contains("no match for (f (c))"), "{e}");
    let before = run(DECLS).unwrap().eg.node_count();
    let after = run(&format!("{DECLS}(check (a))")).unwrap().eg.node_count();
    assert_eq!(before, after, "a check adds no node");
}

#[test]
fn check_variables_are_existential() {
    let base = format!("{DECLS}(let t (f (a)))\n");
    run(&format!("{base}(check (= e (f x)))")).unwrap();
    run(&format!("{base}(check (= t (f x)))")).unwrap();
    run(&format!("{base}(check (= t (f x)) (= x (b)))")).unwrap();
    let e = run(&format!("{base}(check (= t (f x)) (= x (c)))"))
        .err()
        .expect("no join");
    assert!(e.contains("no match"), "{e}");
    // A variable is scoped to its check: the next check may reuse the name freely.
    run(&format!("{base}(check (= e (f x)))\n(check (= e (a)))")).unwrap();
}

#[test]
fn check_names_follow_rule_bodies() {
    // A bare name of an operator or sort is not a variable: egglog reports the same as
    // shadowing, and here it also catches a nullary term written without parentheses.
    let e = run(&format!("{DECLS}(check (= e (f a)))"))
        .err()
        .expect("operator");
    assert!(e.contains("`a` names an operator"), "{e}");
    let e = run(&format!("{DECLS}(check (= E (f (a))))"))
        .err()
        .expect("sort");
    assert!(e.contains("`E` names a sort"), "{e}");
}

#[test]
fn a_variable_used_once_is_reported() {
    let base = format!("{DECLS}(let t (f (a)))\n");
    let i = run(&format!("{base}(check (f x))")).unwrap();
    assert!(
        i.warnings().iter().any(|w| w.contains("`x` occurs once")),
        "{:?}",
        i.warnings()
    );
    let i = run(&format!("{base}(check (f _x))")).unwrap();
    assert!(i.warnings().is_empty(), "{:?}", i.warnings());
    // The bare side of a top-level `(= e p)` names the class and is not reported.
    let i = run(&format!("{base}(check (= e (f (a))))")).unwrap();
    assert!(i.warnings().is_empty(), "{:?}", i.warnings());
}

const LAZY: &str = "
(sort E)
(function add (E) E :assoc :comm)
(function a () E)
(function b () E)
(function c () E)
(function d () E)
(function n () E)
(union (add a b) c)
(union (add a b d) n)
(let t (add c d))
";

#[test]
fn lazy_ac_completes_where_a_check_needs_it() {
    // `(add c d)` and `n` join only through AC completion: `a + b = c` rewrites
    // `a + b + d`, the class of `n`, to `c + d`. Lazy mode keeps the stored graph
    // uncompleted, so each check below has to run completion to see it.
    run_in(&format!("{LAZY}(prove (= n t))"), AcMode::Lazy).unwrap();
    run_in(&format!("{LAZY}(check (= (n) t))"), AcMode::Lazy).unwrap();
    run_in(&format!("{LAZY}(check (= (n) (add (c) x)))"), AcMode::Lazy).unwrap();
    // Without completion the classes stay apart.
    run_in(&format!("{LAZY}(check (= (n) t))"), AcMode::Off)
        .err()
        .expect("apart without completion");
}

#[test]
fn a_lazy_check_leaves_the_graph_as_it_was() {
    let i = run_in(
        &format!("{LAZY}(check (= (n) t))\n(print-size)"),
        AcMode::Lazy,
    )
    .unwrap();
    let plain = run_in(&format!("{LAZY}(print-size)"), AcMode::Lazy).unwrap();
    assert_eq!(i.eg.node_count(), plain.eg.node_count());
}

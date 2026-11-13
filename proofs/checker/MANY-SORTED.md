# Many-sorted semantics for the checker: plan

This document is the plan for extending `goal_sound` from one-sorted models to
the many-sorted algebras a program denotes. It is not a status page: the state
of the code is what `lake build` proves and what the fixture sweep measures.

## The gap

`goal_sound` quantifies over one-sorted models (`Semantics.lean`): a single
carrier, every operator total on it, and every rule required for every
assignment of its variables, including assignments that mix sorts. A
many-sorted algebra of the program (one carrier per sort, operators typed by
their signatures) does not in general extend to such a model, because the
extension must also satisfy each rule for ill-sorted assignments. The theorem
therefore does not state that a certified `check-eq` holds in the program's
models. The earlier README called the one-sorted class "a smaller class than
the many-sorted models of the program"; that sentence was false and is
retracted.

The omitted laws (`:nilpotent`, `:inverse`, `:cancellative`) and primitives
are a different kind of limit: the reader drops them, so the theorem speaks of
a weaker theory whose models include the program's. They cost coverage, not
soundness, and are out of scope here.

## Approach

**One carrier with a sort predicate.** A model keeps one carrier `α` and adds
`dom : Sort → α → Prop`. Operators map well-sorted arguments into their result
sort; the operator laws and the rules are required only inside the domains.
This keeps the kernel's proof free of dependent carrier types, which would
otherwise reach every lemma about `nval` and folds.

**A bridge to genuine many-sorted algebras.** A separate theorem builds such a
model from any algebra with one carrier per sort (carrier `(Σ s, C s) ⊕ junk`,
`dom s` the `s` component, ill-sorted applications sent to `junk`) and shows it
satisfies the program exactly when the algebra does, with the same value on
well-sorted terms. The final theorem is stated over those algebras.

**Laws relative to the domain.** Idempotence and the unit law cannot hold on
elements of other sorts in a disjoint-union carrier, so every law of an
associative operator of sort `s` is required on `dom s` only, with its binary
operation closed on `dom s`.

**Empty sorts.** Many-sorted equational deduction is unsound with empty sorts
when a derivation keeps a variable of an empty sort. The kernel derives
equalities between ground nodes and instantiates a rule only with existing
nodes, so no derivation carries a variable and the problem does not arise.

## Steps

| step | change | checkpoint |
| --- | --- | --- |
| 0 | README: retract the false sentence; state what `goal_sound` covers | commit |
| 1 | Reader: operator signatures (`sort`, `datatype`, `function`, `constructor`, `relation`; a variadic `:assoc` operator over its one argument sort); literals sorted by position (`Term.lit s v`); rule variables sorted by the positions they occupy, through body equalities; a rule with a variable of two sorts or of none becomes `none`; a command's rules become `List (Option Rule)`, so a rule's index does not depend on what the reader drops; goals and `let` terms sort-checked | `lake build` |
| 2 | Semantics: `Model` with `dom`; `OpTyped`; `OpSat` relative to `dom`; `RuleSat` over sorted assignments | `lake build` |
| 3 | Kernel: `wfSorts` (each node's sort; each child of the sort its position takes), checked once with `wfNodes`; the `rule` step checks each `σ x` has the variable's sort | `lake build` |
| 4 | Proof: a well-sorted node's value is in `dom` of its sort; the fold lemmas and `AssocLaws` relative to `dom s`; `goal_sound` over the sorted `Model`, on `propext`, `Classical.choice` and `Quot.sound` only | commit: sorted `goal_sound` |
| 5 | Bridge: `SAlgebra` (a carrier per sort, typed operations, per-sort laws and rules); its `Model`; satisfaction and term values preserved; `goal_sound_sorted` over `SAlgebra` | commit: `goal_sound_sorted` |
| 6 | Writer: literal nodes carry their sort (`n k l i64 6`, from `sort_of`); rule indices follow step 1's numbering | commit |
| 7 | Validation: fixture sweep (20 s and 2 GB per engine run, 60 s and 4 GB per check); a hand-written certificate instantiating a rule with an ill-sorted assignment, accepted before and rejected after; egraph tests and clippy; README and coverage table | commit, push to the fork |

## What is measured

The sweep before this change certifies 157 of the 1,594 `check-eq` that hold,
and every `check-eq` of 62 of 235 fixtures (fork commit `2817e7b1`). After
step 7 the sweep is rerun; every goal lost is explained by its cause (a rule
dropped for a variable whose sort the reader cannot infer, a literal whose
position does not fix its sort).

## Risks

- The literal `6` can be `i64`, `u64`, `usize` or `IBig`: the reader takes the
  sort from the position, and the writer must spell the same sort, or the
  literal's node is not the one the checker interns.
- Sort inference drops some rules the one-sorted reader read, for example a
  variable that occurs only in equalities between variables. Step 7 counts them.
- The relative fold lemmas carry a domain hypothesis through every induction;
  their size is comparable to `Fold.lean`.

## After this

The nilpotent, inverse and cancellative laws are stated on the sorted,
domain-relative `OpSat`, so this change comes first and those laws are proved
once.

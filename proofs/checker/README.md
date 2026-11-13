# semper-check: a Lean checker for equality certificates

`semper-check PROGRAM.egg CERT` reads a program and a certificate the engine
wrote (`semi-persistent --proofs --cert CERT PROGRAM.egg`), checks every step
of the certificate, and reports which `check-eq` commands of the program the
certificate proves. The checker is a Lean 4 program with no dependency beyond
Lean's core library; `lake build` builds it in under a minute.

## What a proved `check-eq` means

`goal_sound` (`SemperCheck/Sound.lean`) states it: if every step checks and
the certificate lists a step for the `check-eq l r` at byte offset `o`, then
`l = r` holds in every model of the program's operator laws and of the
`union` commands and rules that start before `o`. A model
(`SemperCheck/Semantics.lean`) interprets each operator as a function on one
carrier; it satisfies an `assoc`, `ac` or `aci` operator's laws when the
operator's applications fold an associative binary operation (commutative for
`ac` and `aci`, idempotent for `aci`) with the declared identity as its unit,
and a `comm` operator's when it is symmetric in its two arguments. A rule
holds in a model when its two sides are equal under every assignment that
makes its equality premises hold.

The theorem depends on Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) and on no `sorry`. The trusted part is the
statement (`Syntax.lean`, `Semantics.lean`), the `.egg` reader
(`Parse.lean`), Lean's kernel, and Lean's compiler, which runs the checker.

## The kernel

A certificate is a table of nodes, each a literal or an operator over earlier
nodes, and a list of steps, each concluding that two nodes are equal
(`SemperCheck/Kernel.lean`):

| step | conclusion |
| --- | --- |
| `refl a` | `a = a` |
| `symm s`, `trans s t` | from earlier steps |
| `axiom o a b` | the `union` at offset `o` has the terms `a` and `b` |
| `rule o j σ prems a b` | rule `j` of the command at `o`, instantiated by `σ`, has sides `a` and `b`; `prems` prove its equality premises |
| `cong f a b prems` | `a` and `b` are equal modulo the laws of `f`, after replacing each premise's left node by its right node |

`cong` covers congruence (children pairwise equal), a commutative operator's
swapped children, and the associative operators: both sides flatten to their
arguments, the premises rewrite each argument (an argument rewritten to an
application of the same operator is flattened again), the unit is removed,
and the two results are compared as lists (`assoc`), multisets (`ac`) or sets
(`aci`). Every conclusion records the offsets of the commands it cites, so a
`check-eq` can use only the commands before it.

## What the reader reads

The reader (`Parse.lean`) keeps the theory it returns implied by the
program's: it drops the algebraic tags it does not model (`:nilpotent`,
`:inverse`, `:cancellative`, `:assoc-left`, `:assoc-right`), and it reads no
rule from a command whose pattern or guard uses a rest variable, a
multiplicity, a filter, a primitive predicate or a comprehension. Dropping a
law or a rule makes some certificates fail to check; it never makes a false
equality check. A program with `push`, `pop` or `include` is rejected.

The sorts are not modelled: the theorem quantifies over one-sorted models,
in which every operator is total on one carrier and every rule holds for
every assignment, including one that mixes sorts. A many-sorted algebra of
the program does not in general extend to such a model, so the theorem does
not yet state that a certified `check-eq` holds in the program's many-sorted
models. An earlier version of this README called the one-sorted models "a
smaller class than the many-sorted models of the program"; that claim is
false and retracted. `MANY-SORTED.md` is the plan that closes the gap.

## Coverage over the fixtures

Over the fixtures of `egraph/tests/egg`, each run with `--proofs --cert`
(release build, 20 s and 2 GB per run) and then checked: the checker proves
157 of the 1,594 `check-eq` that hold, and every `check-eq` of 62 of the 235
fixtures that have one. No step the writer emits fails to check.

A step that does not check concludes only `0 = 0` (`Ctx.failed` in
`Kernel.lean`), and the checker reports it: a mistake in the writer costs the
goals whose derivations cite the step, not the whole certificate.

The writer leaves a goal unproved when an edge on its explanation is one it
cannot express. Counted by edge (an edge can block several goals, and a goal
stops at its first such edge):

| edge | count |
| --- | --- |
| a law or completion step whose two sides the writer cannot relate by flattening and by rewriting arguments to class members (nilpotent and inverse laws, inter-reduction) | 809 |
| a rule the checker's reader reads no rule from: a primitive operation or guard, a rest variable, a multiplicity, a `:let` | 202 |
| cancellation | 127 |
| a rule application whose pattern the writer cannot match to the two nodes by position (most in the `flatten` fixtures, where the engine matched modulo associativity) | 35 |
| a sequence rule, which carries no source position | 19 |
| a law step between two nodes of no associative operator | 13 |

A lazy `check-eq` runs completion in a transaction that the next command
discards; the interpreter proves the pending goals into the certificate
(`EGraph::cert_prove_goals`) before it restores, and the writer then drops
its memo entries for the discarded node ids (`EGraph::cert_forget`).

For a rule application, the writer reads the rule's command as the checker
reads it, matches the rule's sides to the edge's two nodes modulo their
classes (either child order for a commutative operator) to recover the variable bindings, and joins the instance to the two
nodes by `cong` steps whose premises are forest paths.

An empty application `(Add)` is the unit in the engine; the semantics does
not state that law, so the fixtures that check it stay unproved. Six fixtures
do not parse: two use `push` and `pop`, four write a count above 65,536.

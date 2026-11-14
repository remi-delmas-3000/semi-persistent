# semper-check: a Lean checker for equality certificates

`semper-check PROGRAM.egg CERT` reads a program and a certificate the engine
wrote (`semi-persistent --proofs --cert CERT PROGRAM.egg`), checks every step
of the certificate, and reports which `check-eq` commands of the program the
certificate proves. The checker is a Lean 4 program with no dependency beyond
Lean's core library; `lake build` builds it in under a minute.

## What a proved `check-eq` means

`goal_sound` (`SemperCheck/Sound.lean`) states it: if every step checks and
the certificate lists a step for the `check-eq l r` at byte offset `o`, then
`l = r` holds in every model of the program's operator signatures and laws
and of the `union` commands and rules that start before `o`.

A model (`SemperCheck/Semantics.lean`) is many-sorted: it has one carrier and
a predicate `dom s` for the elements of each sort `s`. Each operator sends
arguments of its argument sorts to an element of its result sort, and each
literal of a literal sort (`i64`, `String`, ...) is an element of that sort.
The laws are required only on elements of the operator's sort: an `assoc`,
`ac` or `aci` operator folds a binary operation that is closed on its sort
and associative there (commutative for `ac` and `aci`, idempotent for `aci`),
with the declared identity as its unit and as the value of the empty
application; a `comm` operator is symmetric on well-sorted arguments. A rule
holds when its two sides are equal under every assignment of its variables to
elements of their sorts that makes its equality premises hold. A many-sorted
algebra of the program gives such a model by taking the disjoint union of its
carriers; the plan in `MANY-SORTED.md` adds that construction as a theorem.

The theorem depends on Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) and on no `sorry`. The trusted part is the
statement (`Syntax.lean`, `Semantics.lean`), the `.egg` reader
(`Parse.lean`), Lean's kernel, and Lean's compiler, which runs the checker.

**Why the sorts matter.** `tests/empty_sort.egg` declares a sort `A` with no
constructor, `f : A -> C`, and the rules `(f x) -> (c)` and `(f y) -> (d)`.
In a many-sorted model where `A` is empty both rules hold and `c` and `d`
differ. The one-sorted checker of commit `89b9e8a2` accepted
`tests/empty_sort.cert`, which instantiates both rules with the node `c` (of
sort `C`) for the variable and derives `c = f(c) = d`; the many-sorted checker
rejects it, because `f(c)` is ill-sorted.

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
`:inverse`, `:cancellative`), and it reads no rule from a command whose
pattern or guard uses a rest variable, a multiplicity, a filter, a primitive
predicate or a comprehension. Dropping a law or a rule makes some
certificates fail to check; it never makes a false equality check. A program
with `push`, `pop` or `include` is rejected.

Sorts come from the declarations (`sort`, `datatype`, `function`,
`constructor`, `relation`). A literal takes the sort of its position (`6` in
`(Num 6)` is an `i64` when `Num` takes one), or the engine's default for its
spelling where no position fixes it. A rule variable takes the sort of the
positions it occupies, through the body's equalities; a rule with a variable
of two sorts or of none is not read. A command keeps one entry per rule it
states, `none` for one not read, so a certificate cites a rule by a position
that does not depend on what the reader drops. A program whose term is
ill-sorted, or that applies an `:assoc-left` or `:assoc-right` operator to
more arguments than its signature takes, is rejected; the latter is a
limitation of the reader (8 fixtures), not of the semantics.

## Checking every regression program

`scripts/check-certificates.py` has the engine write a certificate for every
program the regression tests run and expect `ok`, and checks each one: the
files `egraph/tests/egg_tests.rs` registers, the CBMC and conformance corpora,
and the book examples. CI runs it (`.github/workflows/checker.yml`). It fails
on a step that does not check, a rejected certificate, an engine failure
under `--proofs`, or a program proving fewer `check-eq` than
`coverage.tsv` records; `--update` rewrites `coverage.tsv` after a change
that proves more.

Over the 1,684 programs (release build, 60 s and 4 GB per run, 61 s wall
time with six jobs): 1,441 certificates check with no failed step, 5,697 of
the 29,807 `check-eq` they cover are proved, and every `check-eq` of 201 of
the 1,065 programs with one. 125 programs expect an outcome other than `ok`.
The reader rejects 117 programs: 101 apply an `:assoc-left` or
`:assoc-right` operator to more arguments than its signature takes (93 of
them in the `conform-flatten` corpus), 8 use `push` and `pop`, 5 write a
count above 65,536, and 2 use an unannotated literal where its default sort
is not the one the position takes. One program, `bench/acgen.rules.egg`,
exceeds 4 GB under `--proofs`; it runs in 9 s without proofs, and
`bench/search-dfs-small.rules.egg`, which the regression tests do not
register, takes over 120 s under `--proofs` against 2 s without, on the
engine before this branch too.

## Coverage over the fixtures

Over the fixtures of `egraph/tests/egg`, each run with `--proofs --cert`
(release build, 20 s and 2 GB per run) and then checked: the checker proves
157 of the 1,579 `check-eq` that hold in the programs it reads, and every
`check-eq` of 62 of the 228 such fixtures that have one. No step the writer emits fails to check.

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
not state that law, so the fixtures that check it stay unproved. Fourteen
fixtures do not parse: two use `push` and `pop`, four write a count above
65,536, and eight apply an `:assoc-left` or `:assoc-right` operator to more
arguments than its signature takes.

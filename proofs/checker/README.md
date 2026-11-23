# semper-check: a Lean checker for the engine's equalities

`semper-check --replay PROGRAM.egg TRACE` reads a program and the stream of
events the engine wrote while it ran it (`semi-persistent --proofs --trace
TRACE PROGRAM.egg`), replays the stream, and reports which `check-eq` commands
of the program it proves. `semper-check PROGRAM.egg CERT` checks a certificate
(nodes and steps, `Parse.lean`) directly. The checker is a Lean 4 program with
no dependency beyond the Lean toolchain's own libraries; `lake build` builds
it in under a minute.

The replayer (`Replay.lean`, specified in `REPLAY.md`) keeps its own node
table and its own union-find over node ids, reads the stream in order, and
checks each event against its own classes. It is proved sound
(`ReplaySound.lean`): after any stream, two nodes it holds in one class have
one value in every model of the program (`replay_classes`), and a `check-eq`
it reports as proved holds in every model of the commands before it
(`replay_sound`). The theorems are about `Replay.step`, the function the
executable runs on each line, and assume nothing about the stream.

## How the replayer is proved

The table, the classes and the proved `check-eq` are a `Core P`
(`Core.lean`): a state that carries its invariant, and that only eight
operations build, each with a proof that it keeps the invariant. A node
enters the table if it is well-sorted. A kernel step's conclusion is recorded
if the kernel's check (`Kernel.lean`, proved in `Sound.lean`) accepts the
step. Two classes are joined only by a link that a recorded conclusion
proves. A `check-eq` is recorded if a recorded conclusion is that equality,
from commands before it.

An event's check is the construction of the kernel steps for its merge, from
the event's witnesses and the classes, followed by the link. The rest of
`Replay.lean` (1,900 lines) decides which steps to build; it has no way to
build a `Core P` except through the eight operations, so nothing about it is
assumed: a wrong construction yields a step the kernel does not accept, and
the merge is not applied. No definition of the replayer is `partial`.

## What a proved `check-eq` means

`replay_sound` (`SemperCheck/ReplaySound.lean`) states it: if the replay of a
stream records the `check-eq l r` at byte offset `o` as proved, then `l = r`
holds in every model of the program's operator signatures and laws and of the
`union` commands and rules that start before `o`. `goal_sound`
(`SemperCheck/Sound.lean`) is the same statement for a certificate checked
directly.

A model (`SemperCheck/Semantics.lean`) is many-sorted: it has one carrier and
a predicate `dom s` for the elements of each sort `s`. Each operator sends
arguments of its argument sorts to an element of its result sort, and each
literal of a literal sort (`i64`, `String`, ...) is an element of that sort.
The laws are required only on elements of the operator's sort: an `assoc`,
`ac` or `aci` operator folds a binary operation that is closed on its sort
and associative there (commutative for `ac` and `aci`, idempotent for `aci`),
with the declared identity as its unit and as the value of the empty
application; with `:inverse g` and a unit, `g` gives an inverse for every
element of the sort; with `:nilpotent n` and a unit, `n` copies of an element
make the unit; with `:cancellative`, `b x z = b y z` gives `x = y`. A `comm`
operator is symmetric on well-sorted arguments. A rule
holds when its two sides are equal under every assignment of its variables to
elements of their sorts that makes its equality premises hold. A many-sorted
algebra of the program gives such a model by taking the disjoint union of its
carriers; the plan in `MANY-SORTED.md` adds that construction as a theorem.

The theorems depend on Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) and on no `sorry`. The trusted part is the
statement (`Syntax.lean`, `Semantics.lean`, `Prim.lean`), the `.egg` reader
(`Parse.lean`), Lean's kernel, and Lean's compiler, which runs the checker.
The engine and the stream are not trusted.

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
| `inv f a x q e` | `a = f(x, q)` with `q = g(x)` is the unit `e` of `f`, whose `:inverse` is `g` |
| `nil f a x k e` | `a = f(x, .., x)`, with `k + 1` arguments, is the unit `e` of `f`, which is `:nilpotent (k + 1)` |
| `cancel f s a b z` | step `s` concludes `f(a, z) = f(b, z)`, so `a = b`: `f` is `:cancellative`, or has `:inverse` and a unit |
| `unit f a e` | `a = f()`, the application to no argument, is the unit `e` of `f` |
| `prim f a e` | `a = f(c1, .., ck)`, a primitive applied to literals, is the literal `e` that `primOk` computes |
| `seq o B a b` | the sequence rule of the command at `o`, under the binding `B`, yields the terms that are nodes `a` and `b` (`seqApply`) |

For a comb operator (`:assoc-left`, `:assoc-right`), `cong` reads each node
through its first argument (left) or its last (right) when that argument is an
application of the same operator, and compares the two argument lists position
by position, each pair equal or a premise.

`cong` covers congruence (children pairwise equal), a commutative operator's
swapped children, and the associative operators: both sides flatten to their
arguments, the premises rewrite each argument (an argument rewritten to an
application of the same operator is flattened again), the unit is removed,
and the two results are compared as lists (`assoc`), multisets (`ac`) or sets
(`aci`). Every conclusion records the offsets of the commands it cites, so a
`check-eq` can use only the commands before it.

## Primitives

A model interprets a primitive applied to literals as the literal the
primitive computes: `Models` asks `M.app f (lits) = M.lit out` whenever
`primOk f lits out` holds. `Prim.lean` defines `primOk` by an evaluator for
every operation of `egraph/src/model.rs` (`bool`, `i64`, `u64`, `usize`,
`f64`, `String`, `IBig`, `UBig`, `RBig`), ported operation by operation: a
checked operation has no value on overflow or a zero divisor, a wrapping one
reduces modulo 2^64, floats are Lean's `Float` (IEEE-754 binary64) under the
engine's total order. The evaluator is part of the statement: no theorem
relates it to the engine's table, and a disagreement shows as a goal the
replay does not prove (the stream's literal is not the one `primOk` accepts).
Where the evaluator is narrower than the engine it gives no value: a string
literal with a backslash, and `RBig::pow` with an exponent above 4,096.
`usize` is taken as 64 bits wide.

A primitive in a rule is an operator: the reader declares it with the
signature `primSig` gives. A primitive guard `(i64::< a b)` is the equality
premise `(i64::< a b) = true`. A multiplicity variable read as a value
(`(RBig::scale a k)`) is the pattern `count k`, the `i64` literal that spells
the count. The reader gives each literal of the program the spelling the
stream uses for its value (`canonLit`: `0/1` is `0`, `4.0` is `4`).

## Sequence rules

A rule whose left side has a filter `(..g p)` is a sequence rule. Its meaning
in the statement is given by an evaluator (`Seq.lean`, `seqApply`): under a
binding (the rest sequences, each filter's elements with the values of the
pattern's variables at each element, the scalars), the rule yields a left
term (the root operator applied to the rest atoms and to one instance of `p`
per element) and a right term built from the same elements. A model satisfies
the rule when the two terms are equal under every binding and every valuation
of the binding's atoms (`SeqSat`). The statement does not ask that a filter's
elements be all the arguments that match `p`, and it does not restrict the
atoms to their sorts: a model must satisfy more instances than the engine
fires. A `:when` condition is part of the rule: `seqApply` yields nothing
under a binding for which a condition does not compute `true` (`numS`: a
literal, a scalar, `(count g)`, a primitive). `:except` is read and adds
nothing, since a binding names each filter's elements. The reader reads a
sequence rule with no tag but `:when`, a filter with or without a count
(`..g:k`, `..g:k>=n`, whose least count `seqApply` checks; `(sum k)` is the
sum of the elements' counts), and a right side of variables, literals,
applications, splices `..x`, computed literals, counted arguments `t:k`, and
comprehensions `..[ t for x in s if c ]` and `..{ t:k for x:n in s }` over a
filter's elements, a column, a rest sequence, `(zip ..)` or `(concat ..)`. A
comprehension's condition and count are computed on the binding by the same
evaluator. A rule with a comprehension and no filter is a sequence rule whose
left side is a pattern: its binding is read from the match's `e` lines, and
equal neighbours of a rest sequence are one row with their number as count.

The evaluator also reads: `:let` names (each the literal its value is, in
order); `min`, `max` and `sum` of a value over the filters' elements; `(if c a
b)`; the number of rows of a source; and two interval operations ported from
`egraph/src/seq_rhs.rs`: `(union-by p l u)` (per value of `p`, the union of
the integer intervals `[l, u]`, intervals that touch being one) and `(narrow c
d r a b q)` (each `[c, d]` shrunk past the intervals `[a, b]` whose `q` is its
`r`; `narrowed` keeps the rows that changed). Values of `p`, `r`, `q` are
compared as atoms of the binding. Integer bounds are unbounded integers here;
the engine reports an overflow of the literal sort as an error. `:flatten` and
`:except` are read and add nothing to the rule: they say which arguments the
engine collects, and a binding names them. For a firing of a `:flatten`
sequence rule that read one root argument through a member of its class, the
replay builds the member from the binding (the application of the bound
arguments no other root argument answers) and checks that it is in that
argument's class. A firing that read several arguments through is not proved.

## What the reader reads

An `:assoc-left` or `:assoc-right` operator takes any number of arguments of
its sort. In a model it is a comb of one binary operation with no law:
`(L a b c)` is `b(b(a, b), c)` under `:assoc-left` and `b(a, b(b, c))` under
`:assoc-right` (`OpSat`, kinds `foldL` and `foldR`). `(L (L a b) c)` and
`(L a b c)` are then equal by the fold itself, and `(L a (L b c))` is not.
A unit, inverse or other tag on such an operator is not read.

`(push)` and `(pop)` are read. The program records each pair of offsets
(`Program.pops`), and a command is in force at an offset when no scope that
holds it was closed before that offset (`Program.active`). `Models P p` asks
a model to satisfy the commands before `p` that are in force at `p`, so a
`check-eq` after a `(pop)` does not get the scope's unions and rules as
premises. The kernel keeps each conclusion's offset and combines two
conclusions, or accepts one for a goal, only when no scope that holds the
earlier offset was closed before the later one (`Program.stays`). Operators
declared inside a scope stay in the program's signature. `(include)` is not
read.

In a matched pattern a bare name is a variable, also when a nullary operator
has that name (`(rewrite (f a) (g a))` matches `(f (b))`); in a built side a
bare name no pattern bound is the operator. The engine reads them so.
In a built side, a nested application of the same `:assoc` operator is read
as its arguments, as the engine's builder splices them; associativity makes
the two terms equal. A rule whose right side has an argument with a computed
count (`t:(u64::- k 1)`) is read as a sequence rule.

The reader (`Parse.lean`) keeps the theory it returns implied by the
program's: it reads no rule from a command whose
pattern or guard uses a filter or a comprehension. A
count on an argument of an `assoc`, `ac` or `aci` operator is read: `x:6` is
six arguments, and `x:k` (or `x:k>=2`) repeats the argument as many times as
the multiplicity variable `k`, which in a model ranges over the counts from 1
(or from the constraint's bound). A rest variable `..r` is read as an argument of an `assoc`,
`ac` or `aci` operator: in a model the rule holds for every list of elements
of the operator's sort in its place, the empty one included. Dropping a law or a rule makes some
certificates fail to check; it never makes a false equality check. A program
with `include` is rejected.

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

## Replaying every regression program

`scripts/check-replay.py` has the engine write the stream of every program the
regression tests run and expect `ok` (the files `egraph/tests/egg_tests.rs`
registers, the CBMC and conformance corpora, and the book examples), and
replays each one. CI runs it (`.github/workflows/checker.yml`). It fails on an
engine failure under `--proofs`, a replay that does not finish, a step the
kernel rejects, or a program that proves fewer `check-eq` than `coverage.tsv`
records; `--update` rewrites `coverage.tsv` after a change that proves more.
`scripts/test-replay.py` replays the fixtures of `tests/replay`: for each kind
of line, a stream that proves its goal and the same stream with one witness
changed, which costs the goal that depends on it.

Over the 1,684 programs (release build, 60 s and 4 GB per run, four jobs, 27 s
of wall time): 1,554 are replayed, 125 expect an outcome other than `ok`, and
the reader rejects 5, which write a count above 65,536.

| | count |
| --- | --- |
| `check-eq` proved (`replay_sound` covers them), of 31,099 | 31,096 |
| programs with every `check-eq` proved, of 1,161 | 1,158 |
| kernel steps checked | 16,635,974 |
| steps the kernel rejects | 0 |
| events replayed | 7,438,518 |
| events whose check fails | 8,069 |
| events the stream gives no witness for | 347 |

`GAP.md`, which `check-replay.py --gap` writes, assigns each `check-eq` not
proved to one cause: that of its program's first event that fails, has no
witness, or gets no kernel step. `check-replay.py --failed FILE` lists every
failed event.

The certificates this replaces proved 5,702 `check-eq`, and the replay before
the replayer was proved 21,066. No program proves fewer than under either.

Cost: the 1,442 streams total 235 MB; the median is 1.3 kB and the largest
94 MB. The slowest replay takes 16.0 s and the largest 745 MB; `bench/acgen.rules.egg` (1,120,646
events, a 50 MB stream, 6,647,265 kernel steps, every event checked) takes
11.4 s and 539 MB. With the stream on, the engine runs that benchmark in
11.7 s and 706 MB against 10.6 s and 704 MB in proof mode without it, and
`bench/search-dfs-small.rules.egg` in 2.2 s and 11.6 MB against 2.1 s and
11.4 MB, with a 47 kB stream (two runs each).

`SEMPER_REPLAY_SHOW=n` prints the first `n` failed events (a failed completion
event with the monomials it reached), merges without kernel steps and
`check-eq` not proved; with `SEMPER_REPLAY_NODES` set, it
also prints the table id, class root and definition of each node a failed
event names.

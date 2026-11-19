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
statement (`Syntax.lean`, `Semantics.lean`), the `.egg` reader
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

`cong` covers congruence (children pairwise equal), a commutative operator's
swapped children, and the associative operators: both sides flatten to their
arguments, the premises rewrite each argument (an argument rewritten to an
application of the same operator is flattened again), the unit is removed,
and the two results are compared as lists (`assoc`), multisets (`ac`) or sets
(`aci`). Every conclusion records the offsets of the commands it cites, so a
`check-eq` can use only the commands before it.

## What the reader reads

The reader (`Parse.lean`) keeps the theory it returns implied by the
program's: it reads no rule from a command whose
pattern or guard uses a multiplicity, a filter, a primitive predicate or a
comprehension. A rest variable `..r` is read as an argument of an `assoc`,
`ac` or `aci` operator: in a model the rule holds for every list of elements
of the operator's sort in its place, the empty one included. Dropping a law or a rule makes some
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
of wall time): 1,442 are replayed, 125 expect an outcome other than `ok`, and
the reader rejects 117 (101 apply an `:assoc-left` or `:assoc-right` operator
to more arguments than its signature takes, 8 use `push` and `pop`, 5 write a
count above 65,536, and 2 use an unannotated literal where its default sort is
not the one the position takes).

| | count |
| --- | --- |
| `check-eq` proved (`replay_sound` covers them), of 29,808 | 26,852 |
| programs with every `check-eq` proved, of 1,066 | 865 |
| kernel steps checked | 16,387,263 |
| steps the kernel rejects | 0 |
| events replayed | 7,396,100 |
| events whose check fails | 13,441 |
| events the stream gives no witness for | 1,550 |

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

# semper-check: a Lean checker for the engine's equalities

`semper-check --replay PROGRAM.egg TRACE` reads a program and the stream of
events the engine wrote while it ran it (`semi-persistent --proofs --trace
TRACE PROGRAM.egg`), replays the stream, and reports which `check-eq` commands
of the program it proves. `semper-check PROGRAM.egg CERT` checks a certificate
(nodes and steps, `Parse.lean`) directly. The checker is a Lean 4 program with
no dependency beyond the Lean toolchain's own libraries; `lake build` builds
it in under a minute.

The replay has two parts. The replayer (`Replay.lean`, specified in
`REPLAY.md`) follows the stream with its own classes and, for each merge,
emits steps for the kernel. The kernel (`Kernel.lean`) checks the steps. Only
the kernel is proved: `replay_sound` (`ReplaySound.lean`) states that a
`check-eq` the kernel accepts from a replay holds in every model of the
commands before it, whatever the stream and whatever the replayer did. It is
`goal_sound` applied to the steps the replayer emitted.

## What a proved `check-eq` means

`goal_sound` (`SemperCheck/Sound.lean`) states it: if every step checks and
the certificate lists a step for the `check-eq l r` at byte offset `o`, then
`l = r` holds in every model of the program's operator signatures and laws
and of the `union` commands and rules that start before `o`. `replay_sound`
(`SemperCheck/ReplaySound.lean`) is the same statement for the `check-eq` that
`semper-check --replay` reports as proved by the kernel.

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

Both theorems depend on Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) and on no `sorry`. The trusted part is the
statement (`Syntax.lean`, `Semantics.lean`), the `.egg` reader
(`Parse.lean`), Lean's kernel, and Lean's compiler, which runs the checker.
The replayer and the engine are not trusted.

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

## Replaying every regression program

`scripts/check-replay.py` has the engine write the stream of every program the
regression tests run and expect `ok` (the files `egraph/tests/egg_tests.rs`
registers, the CBMC and conformance corpora, and the book examples), and
replays each one. CI runs it (`.github/workflows/checker.yml`). It fails on an
engine failure under `--proofs`, a replay that does not finish, a rejected node
table, or a program that proves fewer `check-eq` through the kernel than
`coverage.tsv` records; `--update` rewrites `coverage.tsv` after a change that
proves more. `scripts/test-replay.py` replays the fixtures of `tests/replay`:
for each kind of line, a stream the kernel accepts and the same stream with one
witness changed, which costs the goal that depends on it.

Over the 1,684 programs (release build, 60 s per run, six jobs, about two
minutes of wall time): 1,442 are replayed, 125 expect an outcome other than
`ok`, and the reader rejects 117 (101 apply an `:assoc-left` or `:assoc-right`
operator to more arguments than its signature takes, 8 use `push` and `pop`, 5
write a count above 65,536, and 2 use an unannotated literal where its default
sort is not the one the position takes).

| | count |
| --- | --- |
| `check-eq` the kernel proves (`replay_sound` covers them), of 29,808 | 20,729 |
| programs with every `check-eq` proved, of 1,066 | 603 |
| kernel steps checked | 12,523,913 |
| `check-eq` the replayer joins | 25,416 |
| events replayed | 7,396,094 |
| events whose check fails | 213,130 |
| merges the replayer does not check | 292,225 |

The 9,079 `check-eq` the kernel does not prove:

- 3,252 are in the 267 programs with a rule firing the stream writes as opaque:
  a rule with a primitive, a rest variable or a multiplicity variable, which
  the reader does not read (292,221 such merges, 287,931 of them in
  `bench/math-microbenchmark.native.egg`). Later events of these programs fail
  because the merge was not applied.
- 4,687 are joined by the replayer through a merge it has no kernel step for:
  11,744 merges, of which 4,810 inter-reductions, 3,575 law steps and 3,233
  critical pairs. The step builder does not finish them; the largest groups are
  merges through a class that holds its own application, and cancellation
  without a unit.
- The rest are in programs where a check fails first: a law step whose
  arguments differ (most after an opaque firing), a rule firing the walk does
  not follow, a completion merge.

The certificates this replaces proved 5,702 `check-eq`. `coverage.tsv` is
higher for 565 programs (15,041 `check-eq`) and lower for 6 (14 `check-eq`),
each with the cause in its row.

Cost: the 1,442 streams total 235 MB; the median is 1.2 kB and the largest
94 MB. The slowest replay, kernel run included, takes 21 s
(`conform-cc-cert/cs1_0013.egg`) and the largest 1.05 GB
(`bench/math-microbenchmark.rules.egg`); `bench/acgen.rules.egg` (1,120,646
events, a 50 MB stream, 6,647,265 kernel steps, every event checked) takes
16 s. With the stream on, the engine runs that benchmark in 11.3 s and 706 MB
against 10.4 s and 700 MB in proof mode without it, and
`bench/search-dfs-small.rules.egg` in 2.4 s either way (a 47 kB stream; the
reader does not read that program, so it has no replay).

`check-replay.py --assume` makes the replayer join the classes of the merges
it does not check, which separates a check that fails by itself from one that
fails because an earlier merge was not applied. It does not change what the
kernel proves.

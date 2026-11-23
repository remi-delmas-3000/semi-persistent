# The replay stream: specification

This document specifies the event stream the engine writes under `--trace FILE`
and the check the Lean replayer runs on each event. It is the contract between
`egraph/src/egraph/trace.rs` (the writer) and `proofs/checker/SemperCheck/Replay.lean`
(the replayer). It is not a status page: what is implemented is what the two
files do and what `scripts/check-replay.py` measures.

## Principle

The replayer holds the program (read from the `.egg` file), a table of node
definitions, and a union-find over node ids. It reads the stream in order and
checks each event against its own classes. Its invariant, proved of the
executable (`replay_classes`, see Soundness): two nodes in one class have equal
values in every model of the program.

An event carries a witness for every existential in its check and nothing the
replayer can compute from the program, the earlier events and its classes. No
check searches: each one is a fixed number of class lookups, a sort of a node's
arguments by class, or the instantiation of a pattern, followed by the kernel
steps for the merge. The steps that equate two nodes under an operator's laws
are chosen by a decision list of at most seven constructions, in a fixed order,
each linear in the arguments of the two nodes (`congStepL`): arguments equal
one by one; the two flattened argument lists equal as classes; all of one
node's arguments in the other's class; a node's arguments each named by a
member of its class that is no application of the operator; and the first four
again after the inverse and nilpotent laws reduce both nodes. That reduction
recurses only while the number of arguments it keeps strictly decreases; no
loop has a pass bound.

Consequence: the replayer's classes equal the engine's at each event only if the
stream holds every merge, in order. A merge the replayer rejects is counted,
reported by cause, and not applied; later events that depend on it then fail
too. A rejected event never makes a goal hold.

## Lines

One event per line, fields separated by one space. Node ids are the engine's.
`f` is an operator name, `off` the byte offset of a top-level form of the
program.

| line | meaning |
| --- | --- |
| `n id f c1 .. ck` | definition: node `id` is `f` applied to nodes `c1 .. ck`, the arguments it was created with (`c:m` is an argument of multiplicity `m`) |
| `l id sort text` | definition: node `id` is the literal `text` of sort `sort` |
| `z f u` | node `u` is the unit of `f`; written when the declaration registers it |
| `t id f c1 .. ck` | the program term `f(c1 .. ck)`, whose arguments evaluated to these nodes, evaluated to node `id` |
| `x off a b` | the `union` at `off` merged `a` and `b`, the nodes of its two terms |
| `c a b` | congruence merged `a` and `b` |
| `w a b` | one of `a`, `b` is an application of an operator with laws, merged with the other, the node or class its arguments normalize to |
| `s c m` | splice witness for the next `c`, `w` or `m` line (before an `m` line: an argument a `:flatten` match read through a member of its class): node `m` is in the class of argument `c` and is an application of the same associative operator |
| `s c m k p at` | opening witness for the next `m` line, written by the matcher as it enumerated the `:flatten` views: on the firing's `e` line at position `k`, class `c` is read as the arguments of its member `m`; `p` is the position, among that line's openings, of the opening whose member holds the argument, or `-` for an argument of the matched node itself; `at` is the number of arguments the view held before `m`'s, which tells two openings of one class apart in a sequence |
| `y c m k` | regrouping witness for the next `m` line: on the `e` line at position `k`, the pattern argument bound to class `c` stands for the arguments of its member `m`, which the matched node holds in its place |
| `r off k` | a rule of the command at `off` fired; `k` is `w` for a `rewrite` (its left side is matched) and `r` for a `rule` (both sides of its `union` actions are built) |
| `e id f c1 .. ck` | within a firing: the pattern application `f` matched node `id`, with its argument patterns bound to `c1 .. ck` (`c:m` for an argument pattern of multiplicity `m`, which is the count a multiplicity variable is bound to when the pattern has one; the nodes a rest variable is bound to between `[` and `]`, in the pattern's order); one line per application of the matched patterns, arguments before the application (`f` is `#lit` for a literal pattern) |
| `b id1 .. idk` | within a firing: the nodes the built patterns' applications evaluated to, arguments before the application (`g` before an id marks the node of a `let` name, which stands for the name's whole term) |
| `m j a b` | within a firing: rule `j` of the command merged `a` and `b`, the nodes of its two sides |
| `g off a b` | the `check-eq` at `off` compared `a` and `b`, the nodes of its two terms |
| `mark d`, `restore d`, `rpop d` | the engine marked its state; restored a mark and kept it; restored a mark and dropped it. `d` is the depth of the mark stack after the operation |
| `j m` | inverse witness for the next line: node `m` is an inverse application and stands for its class, which then cancels against `m`'s argument |
| `o` | a completion round starts |
| `i a b n (l r k)..` | inter-reduction merged `a` and `b`: node `n`, in one of the two classes, rewrites by the rules, in order, to the other node |
| `p a b c d h [x] K s1..sK na (l r k).. nb (l r k).. npa (l r k).. (l r k)..` | a critical pair merged `a` and `b` (see below) |
| `v a b n1 n2` | a consequence of the group law merged `a` and `b`; `n1` and `n2` are the inverse applications it rests on (`n2 = n1` when one is enough) |
| `u kind a b` | a merge the replayer does not check (`kind` names the engine's justification) |

A definition line is written when the engine creates the node, so it precedes
every line that names the node. A restore frees the ids of the nodes it
discards; a later node that takes such an id is defined again.

## Checks

`cls(x)` is the replayer's class of node `x`. `args(x)` are the arguments in
`x`'s definition.

**Normal forms of two argument lists** under operator `f`, used by `t`, `c`,
`w`, `e` and `b`. A check compares two lists, and both are normalized with the
same witnesses. For a plain operator: each list, read as classes. For a
commutative operator: the two classes, sorted. For an associative, AC or ACI
operator: an argument is one class unless a witness splices it. The witnesses
are the `s c m` lines (after checking `cls(m) = cls(c)` and that `m` is an
application of `f`) and every application of `f` that appears among the
arguments of either list or nested in one, which witnesses its own class. Each
argument whose class has a witness is replaced by the witness's arguments,
recursively, a class not being expanded inside its own expansion. Then: an
argument `inv(y)` and one argument in `cls(y)` are removed together, for an
operator with `:inverse inv`; the arguments in the unit's class are dropped;
the rest are read as classes; sorted for AC, with each class's count reduced
modulo `n` under `:nilpotent n`; sorted without duplicates for ACI.

| line | check | effect |
| --- | --- | --- |
| `n`, `l` | each argument's id is below the node's | records the definition |
| `z` | `u`'s definition is the declared unit of `f`, argument for argument | records `f`'s unit |
| `t` | `id` is defined and its value is the term's: `id` is an application of `f` and the normal forms of `args(id)` and `c1 .. ck` are equal, or the normal form of `c1 .. ck` is the one class `cls(id)` | records `(f, c1 .. ck) -> id` in the spelling table |
| `x` | evaluating the two terms of the `union` at `off` through the spelling table gives `a` and `b` | merges `a`, `b` |
| `c` | `a` and `b` are applications of one operator whose argument lists have equal normal forms | merges `a`, `b` |
| `w` | the normal form of `args(a)` is the one class `cls(b)`, or `b` is an application of the same operator and the normal forms are equal | merges `a`, `b` |
| `r` .. `m` | walking the matched patterns arguments-first consumes the `e` lines in order: each line's operator is the pattern's, its `c1 .. ck` are in the classes of the nodes the walk assigned to the argument patterns (a variable takes the node of its first occurrence), and `id` is an application of `f` whose `args(id)` and `c1 .. ck` have equal normal forms. Each body equality holds between classes. Walking the built patterns consumes the `b` nodes: each is a node with the value of its application of the nodes below it. Each variable's node has the variable's sort. `a` and `b` are in the classes of the nodes of the rule's two sides | merges `a`, `b` |
| `g` | evaluating the two terms through the spelling table gives `a` and `b` | the goal is proved if `cls(a) = cls(b)` |
| `mark`, `restore`, `rpop` | the mark exists | saves; restores the classes and the spelling table (definitions stay: a definition claims nothing) |
| `u` | none | counted by `kind`; not applied |

**Evaluating a program term through the spelling table.** A literal is its `l`
node. A `let` name is the node its term evaluated to. An application `f(t1 ..
tk)` is the entry of `(f, n1 .. nk)` where `ni` is the node of `ti`. A missing
entry fails the event.

## What a model must satisfy

Each check concludes an equality of values from equalities the invariant already
gives. `c`, `t`, `w`, `e` and `b` use congruence and the operator's laws
(`Fold.lean`); `x` uses the program's `union`; `m` uses the rule, instantiated
by the assignment the walk built, with each variable's node of the variable's
sort.

## Completion merges

A rule of a completion merge is a triple `l r k`: `l` and `r` are nodes of one
class, `l` an application of the operator. Its left side is `l`'s arguments.
Its right side is `r` as one argument when `k = 1` (the engine's atomic class),
and `r`'s own arguments when `k = 0`. The engine has to say which: when `r` is
itself an application of the operator, both readings are terms of the class.

A monomial is a list of argument nodes, each read as its class. **Reducing** a
monomial by the operator's laws drops the arguments in the unit's class,
removes each inverse pair (an inverse application, or a class a `j` witness
stands for, with one argument in the class of its argument), keeps each class
once under ACI, and keeps each class's count modulo `n` under `:nilpotent n`.
**Applying** a rule to a monomial that holds its left side removes the left
side and adds the right side, as many times as the monomial holds the left
side (once under ACI or a nilpotent law; once for a critical pair's own rules),
then reduces without cancelling inverse pairs: the engine cancels them on the
normal form only. A monomial **reaches** a node when, reduced, it has the
classes of the node's arguments, or it is the one class of the node.

`i a b n rules`: `n` is in the class of `a` or of `b`; `n`'s arguments,
reduced and rewritten by the rules, reach the other node.

`p a b c d h [x] K s1..sK ..`: the peak is the monomial `s1..sK`. Side A
rewrites it by its first `na` rules; side B rewrites it, reduced first when
`d = 1`, by its `nb` rules. When `c = 1` the operator is `:cancellative` or has
`:inverse`, and the common part of the two results is removed from both,
except one occurrence of the class of `x` (present when `h = 1`); both sides
must stay non-empty unless the operator has a unit. Side A then rewrites by its
`npa` remaining rules and side B by the rest. Side A reaches `a` and side B
reaches `b`. The peaks the engine writes: the least common multiple of two
rules' left sides (superposition); a left side plus one of its classes
(idempotence), plus the copies that complete a class's count to `n`
(nilpotence), or plus the inverse of one of its classes (group law), with side
B the reduced peak; one or two left sides, with side B rewritten by the rules
and the common part cancelled (cancellation).

`v a b n1 n2`, with `n1 = g(x1)`, `n2 = g(x2)` and `g` the `:inverse` of an AC
operator `f`: `n1` and `n2` are in one class and the merge is of `x1`, `x2`
(`g` is injective); or `x1` is in the class of `n2` and the merge is of `n1`,
`x2` (`g(g(z)) = z`); or `n1` or `x1` is in the unit's class and the merge is of
`n1`, `x1`; or, under `:nilpotent k`, `k - 1` arguments in the class of `x1`
reach one merged node and the other is in the class of `n1`, or the same with
`n1` and `x1` exchanged.

The engine reads a round's monomials through the classes as they are when the
round starts (`o`), and builds the nodes it merges through the classes as they
are at the merge. The replayer does the same: it reads the derivation of an
`i` or `p` line (the monomials, each rewrite, the common part of a
cancellation) on its classes at the last `o` line, and it reads the two ends
(the start is in a merged class, the result is the other merged node, a rule's
two nodes are in one class) on its current classes. The classes at `o` refine
the current ones.

Each check is one construction. Where the engine has two orders, the line's
fields decide: a `w`, `c`, `t` or `e` check drops an inverse application of a
node of the unit's class by itself; a `p` check with `d = 1` (the peak of a
critical pair with a law) cancels the peak's inverse pair before it drops the
unit's arguments; every other reduction drops the unit's arguments first, and
the two sides of a cancellation keep their inverse pairs.

## Soundness

The replayer's table, classes and proved `check-eq` are a `Core P`
(`Core.lean`): a state that carries its invariant and that only proved
operations build.

- **The invariant** (`Raw.Ok`): the table is well-formed and well-sorted; every
  recorded conclusion holds in every model of the commands it cites; every
  link of the union-find, in the current classes, at each mark and at the
  round's start, is the conclusion of a recorded step; every recorded
  `check-eq` holds in every model of the commands before it.
- **The operations**, each with its proof that the invariant is kept:
  `addNode` (a well-sorted node whose children are in the table), `emit` (the
  kernel's `checkStep` accepts a step against the conclusions so far, and its
  conclusion is recorded), `link` (a node points at a smaller one, given a
  recorded conclusion that the two are equal), `mark`, `restore`,
  `roundStart`, `atRound` (classes whose links are recorded conclusions), and
  `goal` (a recorded conclusion is the `check-eq`, from commands before it).
- **An event's check** is the construction of the kernel steps that justify
  its merge, from the line's witnesses and the classes, followed by `link`:
  `axiom` for `x`; `cong` with class premises for `c`, `w`, `t`; `rule` on the
  instance the walk built, joined to the matched and built nodes by `cong`
  steps, for a firing; for `i` and `p`, `cong` steps per rewrite through the
  terms of the monomials on the way; `inv` (`f(x, g(x))` is the unit), `nil`
  (`f` of `n` copies of `x` is the unit) and `cancel` (from `f(a, z) = f(b,
  z)`, `a = b`) for the inverse, nilpotent and cancellation events, each with
  its law in the models (`OpSat`) and its soundness proof (`Sound.lean`). A
  merge whose steps the kernel does not accept is not applied; `semper-check`
  counts it by line kind.

The theorems (`ReplaySound.lean`) are about `Replay.step`, the function the
executable runs on each line, and hold for every state and every line:

- `step_classes`, `replay_classes`: two nodes the replayer holds in one class
  have one value in every model of the program;
- `step_goals`, `replay_sound`: a `check-eq` recorded as proved holds in every
  model of the commands before it.

They depend on `propext`, `Classical.choice` and `Quot.sound`, and assume
nothing about the stream. The part of the replayer outside `Core.lean` chooses
which operations to call; it cannot build a `Core P` any other way, so a wrong
choice loses a goal and cannot prove a false one. Every definition of the
replayer terminates by a structural or well-founded measure; none is `partial`.

## Not in this version

A firing of a rule with a multiplicity variable, a primitive guard, a
comprehension or a disequality is written as `u rewrite:REASON`: the reader
reads no rule from such a command. `GAP.md` counts the `check-eq` each reason
costs.

The table holds an application's arguments as a list, so a multiplicity is that
many arguments. The reader does not read a program that writes a count above
65,536 (5 of the 1,684 programs), and the replayer does not read a line that
does.

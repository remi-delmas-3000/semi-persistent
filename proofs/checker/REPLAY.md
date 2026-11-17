# The replay stream: specification

This document specifies the event stream the engine writes under `--trace FILE`
and the check the Lean replayer runs on each event. It is the contract between
`egraph/src/egraph/trace.rs` (the writer) and `proofs/checker/SemperCheck/Replay.lean`
(the replayer). It is not a status page: what is implemented is what the two
files do and what the sweep measures.

## Principle

The replayer holds the program (read from the `.egg` file), a table of node
definitions, and a union-find over node ids. It reads the stream in order and
checks each event against its own classes. Its invariant: two nodes in one class
have equal values in every model of the program.

An event carries a witness for every existential in its check and nothing the
replayer can compute from the program, the earlier events and its classes. No
check searches: each one is a fixed number of class lookups, a sort of a node's
arguments by class, or the instantiation of a pattern.

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
| `n id f c1 .. ck` | definition: node `id` is `f` applied to nodes `c1 .. ck`, as given when it was created (an n-ary argument of multiplicity `m` is written `m` times) |
| `l id sort text` | definition: node `id` is the literal `text` of sort `sort` |
| `t id f c1 .. ck` | the program term `f(c1 .. ck)`, whose arguments evaluated to these nodes, evaluated to node `id` |
| `x off a b` | the `union` at `off` merged `a` and `b`, the nodes of its two terms |
| `c a b` | congruence merged `a` and `b` |
| `w a b` | node `a`, an application of an operator with laws, was merged with `b`, the node or class its arguments normalize to |
| `s c m` | splice witness for the next `t`, `c` or `w` line: node `m` is in the class of argument `c` and is an application of the same associative operator |
| `i c m` | inverse witness for the next `t`, `c` or `w` line: node `m`, in the class of argument `c`, is the inverse operator applied to one node |
| `r off j` | a rule fired: rule `j` of the command at `off` |
| `e id f c1 .. ck` | within a firing: the pattern application `f` matched node `id`, with its argument patterns bound to `c1 .. ck`; one line per application of the rule's patterns, arguments before the application |
| `b id1 .. idk` | within a firing: the nodes the right-hand side's applications evaluated to, arguments before the application |
| `m a b` | within a firing: the rule merged `a` (the matched node) and `b` (the right-hand side's node) |
| `g off a b` | the `check-eq` at `off` compared `a` and `b`, the nodes of its two terms |
| `push`, `pop` | the engine marked its state; restored the last mark |
| `u kind a b ..` | a merge the replayer does not check yet (`kind` names the engine's justification) |

A definition line appears before the first line that names its node, and again
after a `pop` that discarded it.

## Checks

`cls(x)` is the replayer's class of node `x`. `args(x)` are the arguments in
`x`'s definition.

**Normal form of an argument list** under operator `f`, used by `t`, `c`, `w`,
`e` and `b`. For a plain operator: the list, read as classes. For a commutative
operator: the two classes, sorted. For an associative, AC or ACI operator:
replace each argument that is itself an application of `f` by its arguments,
recursively; replace each argument `c` with a splice witness `s c m` by the
arguments of `m`, after checking `cls(m) = cls(c)` and that `m` is an
application of `f`; drop the arguments in the unit's class; read the rest as
classes; sort them for AC; sort and remove duplicates for ACI; reduce each
class's count modulo `n` for a nilpotent operator of order `n`; remove a pair
`c1`, `c2` with an inverse witness `i c1 m` after checking `cls(m) = cls(c1)`,
that `m` is `inv(y)` and `cls(y) = cls(c2)`.

| line | check | effect |
| --- | --- | --- |
| `n`, `l` | the arguments are defined; the node is well-sorted for `f`'s signature | records the definition |
| `t` | `id` is defined and its value is the term's: `id` is an application of `f` and the normal forms of `args(id)` and `c1 .. ck` are equal, or the normal form of `c1 .. ck` is the one class `cls(id)` | records `(f, c1 .. ck) -> id` in the spelling table |
| `x` | evaluating the two terms of the `union` at `off` through the spelling table gives `a` and `b` | merges `a`, `b` |
| `c` | `a` and `b` are applications of one operator whose argument lists have equal normal forms | merges `a`, `b` |
| `w` | the normal form of `args(a)` is the one class `cls(b)`, or `b` is an application of the same operator and the normal forms are equal | merges `a`, `b` |
| `r` .. `m` | walking the rule's patterns arguments-first consumes the `e` lines in order: each line's operator is the pattern's, its `c1 .. ck` are the nodes the walk assigned to the argument patterns (a variable takes the node of its first occurrence), and `id` is an application of `f` whose `args(id)` and `c1 .. ck` have equal normal forms. Each body equality holds between classes. Walking the right-hand side consumes the `b` nodes the same way. `a` is the node of the left-hand side's root and `b` of the right-hand side's | merges `a`, `b` |
| `g` | evaluating the two terms through the spelling table gives `a` and `b` | the goal is proved if `cls(a) = cls(b)` |
| `push`, `pop` | a `pop` has a matching `push` | saves; restores the definitions, the classes and the spelling table |
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

## Not in this version

The completion merges (inter-reduction, superposition, axiom critical pairs,
inverse cancellation in completion, cancellation) are `u` lines. Their witnesses
are in the goal that tracks this work.

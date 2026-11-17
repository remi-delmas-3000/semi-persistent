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
| `n id f c1 .. ck` | definition: node `id` is `f` applied to nodes `c1 .. ck`, the arguments it was created with (`c:m` is an argument of multiplicity `m`) |
| `l id sort text` | definition: node `id` is the literal `text` of sort `sort` |
| `z f u` | node `u` is the unit of `f`; written before the first application of `f` |
| `t id f c1 .. ck` | the program term `f(c1 .. ck)`, whose arguments evaluated to these nodes, evaluated to node `id` |
| `x off a b` | the `union` at `off` merged `a` and `b`, the nodes of its two terms |
| `c a b` | congruence merged `a` and `b` |
| `w a b` | node `a`, an application of an operator with laws, was merged with `b`, the node or class its arguments normalize to |
| `s c m` | splice witness for the next `c` or `w` line: node `m` is in the class of argument `c` and is an application of the same associative operator |
| `r off k` | a rule of the command at `off` fired; `k` is `w` for a `rewrite` (its left side is matched) and `r` for a `rule` (both sides of its `union` actions are built) |
| `e id f c1 .. ck` | within a firing: the pattern application `f` matched node `id`, with its argument patterns bound to `c1 .. ck`; one line per application of the matched patterns, arguments before the application (`f` is `#lit` for a literal pattern) |
| `b id1 .. idk` | within a firing: the nodes the built patterns' applications evaluated to, arguments before the application (`g` before an id marks the node of a `let` name, which stands for the name's whole term) |
| `m j a b` | within a firing: rule `j` of the command merged `a` and `b`, the nodes of its two sides |
| `g off a b` | the `check-eq` at `off` compared `a` and `b`, the nodes of its two terms |
| `mark d`, `restore d`, `rpop d` | the engine marked its state; restored a mark and kept it; restored a mark and dropped it. `d` is the depth of the mark stack after the operation |
| `u kind a b` | a merge the replayer does not check yet (`kind` names the engine's justification) |

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

## Not in this version

The completion merges (inter-reduction, superposition, axiom critical pairs,
inverse cancellation in completion, cancellation) are `u` lines. Their
witnesses are in the goal that tracks this work. A firing of a rule with a rest
variable, a multiplicity variable or a primitive is written as `u rewrite`: the
reader reads no rule from such a command.

The replayer is executable and not yet covered by a soundness theorem. It uses
`partial` definitions where the proof will need structural ones (`expand`,
`eval`, the pattern walks).

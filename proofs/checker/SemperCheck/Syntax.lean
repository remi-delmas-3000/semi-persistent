/-!
# The program a certificate is checked against

A program is what the checker reads from an `.egg` file: the operators with
their signatures and algebraic laws, and the commands that state equalities
(`union`, the rules) or ask for one (`check-eq`), each at the byte offset of
its top-level form in the source. Sorts are names; a literal carries its sort,
and a rule carries the sort of each of its variables.
-/

namespace SemperCheck

/-- A ground term: a literal of a sort, or an operator applied to arguments. -/
inductive Term where
  | lit (s v : String)
  | app (f : String) (args : List Term)
  deriving Repr, Inhabited

/-- A rule pattern: a ground term with variables. -/
inductive Pat where
  | var (x : String)
  | lit (s v : String)
  | app (f : String) (args : List Pat)
  /-- A rest variable, as an argument of an `assoc`, `ac` or `aci` operator:
  it stands for any number of arguments, none included. -/
  | rest (x : String)
  /-- An argument repeated: `p`, as many times as the multiplicity variable
  `k` says, as an argument of an `assoc`, `ac` or `aci` operator. -/
  | rep (p : Pat) (k : String)
  /-- An argument repeated a fixed number of times: `p`, `n` times. -/
  | times (p : Pat) (n : Nat)
  /-- The count of the multiplicity variable `k`, as the `i64` literal
  that spells it. -/
  | count (k : String)
  deriving Repr, Inhabited

/-- The variables of a pattern. -/
def Pat.vars : Pat → List String
  | .var x => [x]
  | .lit _ _ => []
  | .app _ ps => (ps.attach.map fun ⟨p, _⟩ => p.vars).flatten
  | .rest _ => []
  | .rep p _ => p.vars
  | .times p _ => p.vars
  | .count _ => []

/-- The rest variables of a pattern. -/
def Pat.rests : Pat → List String
  | .var _ => []
  | .lit _ _ => []
  | .app _ ps => (ps.attach.map fun ⟨p, _⟩ => p.rests).flatten
  | .rest x => [x]
  | .rep p _ => p.rests
  | .times p _ => p.rests
  | .count _ => []

/-- The algebraic laws of an operator. `assoc`, `ac` and `aci` operators are
n-ary over their result sort: an application folds a binary operation over
its arguments. -/
inductive Kind where
  | plain
  | comm
  | assoc
  | ac
  | aci
  deriving Repr, DecidableEq, Inhabited

def Kind.isAssoc : Kind → Bool
  | .assoc | .ac | .aci => true
  | _ => false

structure OpDecl where
  name : String
  kind : Kind
  /-- The argument sorts. An `assoc`, `ac` or `aci` operator takes any number
  of arguments of its result sort, and this list is not read. -/
  args : List String
  res : String
  /-- The `:identity` of an `assoc`, `ac` or `aci` operator. -/
  unit : Option Term := none
  /-- `:nilpotent n`: `n` copies of an argument equal the unit. -/
  nilpotent : Option Nat := none
  /-- `:inverse g`: an argument and `g` applied to it equal the unit. -/
  inverse : Option String := none
  /-- `:cancellative`: two applications that share arguments and are equal
  stay equal without them. -/
  cancellative : Bool := false
  deriving Repr, Inhabited

/-- `lhs = rhs` for every assignment of the variables, each to an element of
its sort, under which each pair of `eqs` is equal. -/
structure Rule where
  lhs : Pat
  rhs : Pat
  eqs : List (Pat × Pat) := []
  /-- The sort of each variable. -/
  sorts : List (String × String)
  /-- Each multiplicity variable with the least count it takes: 1, or the
  `n` of a `>=n` constraint. A variable can be listed more than once. -/
  mults : List (String × Nat) := []
  deriving Repr, Inhabited

/-- The variables of a rule. -/
def Rule.vars (r : Rule) : List String :=
  r.lhs.vars ++ r.rhs.vars ++ (r.eqs.map fun e => e.1.vars ++ e.2.vars).flatten

/-- The rest variables of a rule. -/
def Rule.rests (r : Rule) : List String :=
  r.lhs.rests ++ r.rhs.rests ++ (r.eqs.map fun e => e.1.rests ++ e.2.rests).flatten

/-! ## Sequence rules

A sequence rule's left side is one application whose arguments are items: a
rest sequence `..x`, a filter `(..g p)` that stands for any number of
arguments each an instance of the pattern `p`, or one pattern. -/

/-- An atom of a sequence rule's binding: a value named by a number, or a
literal. -/
inductive SAtom where
  | node (n : Nat)
  | lit (s v : String)
  deriving Repr, Inhabited, DecidableEq

/-- A term over atoms: what a sequence rule's side is under a binding. -/
inductive STm where
  | atom (a : SAtom)
  | app (f : String) (args : List STm)
  deriving Repr, Inhabited

inductive SItem where
  | rest (x : String)
  | filter (name : String) (p : Pat)
  | one (p : Pat)
  deriving Repr, Inhabited

/-- What a comprehension ranges over: one sequence (a filter's elements, a
column, a rest sequence), several side by side (to the shortest), several
one after the other, or the rows of an interval operation. -/
inductive SSrc where
  | one (x : String)
  | zip (xs : List String)
  | concat (xs : List String)
  /-- `(union-by p l u)`: per value of column `p`, the union of the integer
  intervals `[l, u]` of its elements; a row is the value and one interval. -/
  | unionBy (p l u : String)
  /-- `(narrow c d r a b q)`: per element of `r`, its interval `[c, d]`
  shrunk past the intervals `[a, b]` of the elements whose `q` is that `r`;
  with `changed`, only the rows whose interval changed (`narrowed`). -/
  | narrow (c d r a b q : String) (changed : Bool)
  deriving Repr, Inhabited

/-- A value a sequence rule computes from its binding: a literal, a scalar
bound to a literal, the number of elements of a filter, or a primitive
applied to such values. -/
inductive SNum where
  | lit (s v : String)
  | var (x : String)
  | count (g : String)
  /-- The sum of the counts of filter `g`'s elements. -/
  | sum (g : String)
  /-- A count (of a multiplicity variable, or of a comprehension's element)
  as a literal of sort `sort`. -/
  | cnt (x : String) (sort : String)
  /-- The number of rows of `src`. -/
  | rows (src : SSrc)
  /-- `e` at each element of the filters, folded by `op` (`min`, `max`,
  `sum`). -/
  | agg (op : String) (e : SNum)
  | prim (f : String) (args : List SNum)
  deriving Repr, Inhabited

mutual

/-- A sequence rule's right side. -/
inductive SRhs where
  | var (x : String)
  | lit (s v : String)
  | app (f : String) (args : List SArg)
  /-- The literal a computed value is. -/
  | val (e : SNum)
  /-- `a` when `c` computes `true`, else `b`. -/
  | ite (c : SNum) (a b : SRhs)
  deriving Repr, Inhabited

/-- An argument of a right-side application: one term, or the splice `..x`
of a filter's elements or of a rest sequence. -/
inductive SArg where
  | tm (t : SRhs)
  | splice (x : String)
  /-- `t`, as many times as `k` computes. -/
  | times (t : SRhs) (k : SNum)
  /-- A comprehension: `body` for each row of `src`, with `binders` bound to
  the row's values and `kvar` to its count (`grouped`: a rest sequence's equal
  neighbours are one row with their number as count), when `guard` computes
  `true`, as many times as `mult` computes (once without it). -/
  | comp (body : SRhs) (binders : List String) (kvar : Option String) (src : SSrc)
      (grouped : Bool) (guard : Option SNum) (mult : Option SNum)
  deriving Repr, Inhabited

end

structure SeqRule where
  /-- The root operator. -/
  op : String
  items : List SItem
  /-- A left side that is a pattern with rest variables and counts and no
  filter: it replaces `op` and `items`. -/
  lhs : Option Pat := none
  /-- For a `rule`: the pattern of its body, which the engine matches. It is
  no part of what the rule yields: the replay reads the binding from its
  match. -/
  body : Option Pat := none
  rhs : SRhs
  /-- The `:when` conditions: each computes `true` for the rule to apply. -/
  guards : List SNum := []
  /-- The `:let` names, in order: each is the literal its value is. -/
  lets : List (String × SNum) := []
  /-- Per filter with a count `:k>=n`: the least count of each of its
  elements. -/
  least : List (String × Nat) := []
  /-- The sort of each variable, for the reader of a binding's literals. -/
  sorts : List (String × String) := []
  deriving Repr, Inhabited

/-- A binding of a sequence rule. -/
structure SBind where
  /-- Each rest sequence, an argument with count `k` given `k` times. -/
  seqs : List (String × List SAtom) := []
  /-- Per filter, the count of each element (1 outside a multiset). -/
  counts : List (String × List Nat) := []
  /-- Each variable of a filter's pattern: its value at each element. -/
  cols : List (String × List SAtom) := []
  /-- Each variable bound once. -/
  scalars : List (String × SAtom) := []
  /-- Each multiplicity variable's count. -/
  kcounts : List (String × Nat) := []
  deriving Repr, Inhabited

/-- A command that states or asks for an equality. -/
inductive Decl where
  /-- `(union l r)`. -/
  | axiom (l r : Term)
  /-- A `rewrite`, `birewrite` or `rule`, as the rules it states, in order;
  `none` stands for a rule the reader does not read, so the position of every
  other rule does not depend on which ones it drops. -/
  | rules (rs : List (Option Rule))
  /-- The sequence rules of a command (`SeqRule`), in order: one for a
  `rewrite`, one per `union` action for a `rule`; `none` for one the reader
  does not read. -/
  | seq (rs : List (Option SeqRule))
  /-- `(check-eq l r)`. -/
  | goal (l r : Term)
  deriving Repr, Inhabited

structure Program where
  ops : List OpDecl
  /-- The sorts whose elements literals denote (`i64`, `String`, ...). -/
  litSorts : List String
  /-- Each command with the byte offset of its top-level form; offsets
  increase along the list. -/
  decls : List (Nat × Decl)
  /-- Each `(push)` with the `(pop)` that closes it, by their offsets: the
  commands between the two are retired once the `pop` is passed. -/
  pops : List (Nat × Nat) := []
  deriving Repr, Inhabited

/-- The command at `o` is in force at offset `p`: no scope that holds `o` was
closed before `p`. -/
def Program.active (P : Program) (o p : Nat) : Bool :=
  P.pops.all fun se => !(decide (se.1 < o) && decide (o < se.2) && decide (se.2 < p))

/-- Every command in force at `q` is in force at `p`: no scope that holds `q`
was closed before `p`. -/
def Program.stays (P : Program) (q p : Nat) : Bool :=
  P.pops.all fun se => !(decide (se.1 < q) && decide (q ≤ se.2) && decide (se.2 < p))

/-- The first declaration of `f`. -/
def Program.opDecl? (P : Program) (f : String) : Option OpDecl :=
  P.ops.find? (·.name == f)

def Program.kind (P : Program) (f : String) : Kind :=
  match P.opDecl? f with
  | some d => d.kind
  | none => .plain

end SemperCheck

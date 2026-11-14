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
  deriving Repr, Inhabited

/-- The variables of a pattern. -/
def Pat.vars : Pat → List String
  | .var x => [x]
  | .lit _ _ => []
  | .app _ ps => (ps.attach.map fun ⟨p, _⟩ => p.vars).flatten

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
  deriving Repr, Inhabited

/-- `lhs = rhs` for every assignment of the variables, each to an element of
its sort, under which each pair of `eqs` is equal. -/
structure Rule where
  lhs : Pat
  rhs : Pat
  eqs : List (Pat × Pat) := []
  /-- The sort of each variable. -/
  sorts : List (String × String)
  deriving Repr, Inhabited

/-- The variables of a rule. -/
def Rule.vars (r : Rule) : List String :=
  r.lhs.vars ++ r.rhs.vars ++ (r.eqs.map fun e => e.1.vars ++ e.2.vars).flatten

/-- A command that states or asks for an equality. -/
inductive Decl where
  /-- `(union l r)`. -/
  | axiom (l r : Term)
  /-- A `rewrite`, `birewrite` or `rule`, as the rules it states, in order;
  `none` stands for a rule the reader does not read, so the position of every
  other rule does not depend on which ones it drops. -/
  | rules (rs : List (Option Rule))
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
  deriving Repr, Inhabited

/-- The first declaration of `f`. -/
def Program.opDecl? (P : Program) (f : String) : Option OpDecl :=
  P.ops.find? (·.name == f)

def Program.kind (P : Program) (f : String) : Kind :=
  match P.opDecl? f with
  | some d => d.kind
  | none => .plain

end SemperCheck

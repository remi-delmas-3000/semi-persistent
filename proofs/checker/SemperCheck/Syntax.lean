/-!
# The program a certificate is checked against

A program is what the checker reads from an `.egg` file: the operators with
their algebraic laws, and the commands that state equalities (`union`, the
rules) or ask for one (`check-eq`), each at the byte offset of its top-level
form in the source. Sorts are not represented: the semantics is one-sorted
(`Semantics.lean`).
-/

namespace SemperCheck

/-- A ground term: a literal or an operator applied to arguments. -/
inductive Term where
  | lit (v : String)
  | app (f : String) (args : List Term)
  deriving Repr, Inhabited

/-- A rule pattern: a ground term with variables. -/
inductive Pat where
  | var (x : String)
  | lit (v : String)
  | app (f : String) (args : List Pat)
  deriving Repr, Inhabited

/-- The algebraic laws of an operator. `assoc`, `ac` and `aci` operators are
n-ary: an application folds a binary operation over its arguments. -/
inductive Kind where
  | plain
  | comm
  | assoc
  | ac
  | aci
  deriving Repr, DecidableEq, Inhabited

structure OpDecl where
  name : String
  kind : Kind
  /-- The `:identity` of an `assoc`, `ac` or `aci` operator. -/
  unit : Option Term := none
  deriving Repr, Inhabited

/-- `lhs = rhs` for every assignment of the variables under which each pair
of `eqs` is equal. -/
structure Rule where
  lhs : Pat
  rhs : Pat
  eqs : List (Pat × Pat) := []
  deriving Repr, Inhabited

/-- A command that states or asks for an equality. -/
inductive Decl where
  /-- `(union l r)`. -/
  | axiom (l r : Term)
  /-- A `rewrite`, `birewrite` or `rule`, as the rules it states. -/
  | rules (rs : List Rule)
  /-- `(check-eq l r)`. -/
  | goal (l r : Term)
  deriving Repr, Inhabited

structure Program where
  ops : List OpDecl
  /-- Each command with the byte offset of its top-level form; offsets
  increase along the list. -/
  decls : List (Nat × Decl)
  deriving Repr, Inhabited

/-- The first declaration of `f`. An undeclared operator has no laws. -/
def Program.opDecl? (P : Program) (f : String) : Option OpDecl :=
  P.ops.find? (·.name == f)

def Program.kind (P : Program) (f : String) : Kind :=
  match P.opDecl? f with
  | some d => d.kind
  | none => .plain

end SemperCheck

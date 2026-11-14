import SemperCheck.Syntax

/-!
# Models of a program

A model has one carrier `α` and a predicate `dom s` for the elements of each
sort `s`. It interprets every operator as a function on `α` that sends
arguments of the operator's argument sorts to an element of its result sort,
and every literal of a literal sort `s` as an element of `s`. The laws and the
rules are required only of elements of the right sorts: an `assoc`, `ac` or
`aci` operator of result sort `s` folds a binary operation that is closed on
`s` and associative there (commutative for `ac` and `aci`, idempotent for
`aci`, with the declared identity as its unit and the value of the empty
application); a `comm` operator is symmetric on well-sorted arguments; a rule
holds for every assignment of its variables to elements of their sorts.

Every many-sorted algebra of the program gives such a model: take the
disjoint union of its carriers as `α`, the component of `s` as `dom s`, and
send ill-sorted applications to any element. So a `check-eq` that holds in
every model of the program, as `goal_sound` (`Sound.lean`) states of the
certified ones, holds in every many-sorted algebra of the program.

The definitions in this file and in `Syntax.lean` are the statement of the
soundness theorem; the reader (`Parse.lean`) is the other trusted part.
-/

namespace SemperCheck

structure Model where
  α : Type
  dom : String → α → Prop
  app : String → List α → α
  lit : String → String → α

namespace Model

variable (M : Model)

def eval : Term → M.α
  | .lit s v => M.lit s v
  | .app f args => M.app f (args.map eval)

def evalP (σ : String → M.α) : Pat → M.α
  | .var x => σ x
  | .lit s v => M.lit s v
  | .app f args => M.app f (args.map (evalP σ))

/-- Each element of `xs` is in the sort at its position. -/
def ArgsIn : List String → List M.α → Prop
  | [], [] => True
  | s :: ss, x :: xs => M.dom s x ∧ ArgsIn ss xs
  | _, _ => False

/-- An operator with fixed arguments sends arguments of its argument sorts to
an element of its result sort. -/
def OpTyped (d : OpDecl) : Prop :=
  d.kind.isAssoc = false → ∀ xs, M.ArgsIn d.args xs → M.dom d.res (M.app d.name xs)

/-- The laws of operator `d`, on the elements of its sorts. -/
def OpSat (d : OpDecl) : Prop :=
  match d.kind with
  | .plain => True
  | .comm => ∀ x y, M.ArgsIn d.args [x, y] → M.ArgsIn d.args [y, x] →
      M.app d.name [x, y] = M.app d.name [y, x]
  | k => ∃ b : M.α → M.α → M.α,
      (∀ x y, M.dom d.res x → M.dom d.res y → M.dom d.res (b x y)) ∧
      (∀ x y z, M.dom d.res x → M.dom d.res y → M.dom d.res z →
        b (b x y) z = b x (b y z)) ∧
      (∀ x xs, M.dom d.res x → (∀ y ∈ xs, M.dom d.res y) →
        M.app d.name (x :: xs) = xs.foldl b x) ∧
      ((k = .ac ∨ k = .aci) → ∀ x y, M.dom d.res x → M.dom d.res y → b x y = b y x) ∧
      (k = .aci → ∀ x, M.dom d.res x → b x x = x) ∧
      (∀ u, d.unit = some u → M.dom d.res (M.eval u) ∧ M.app d.name [] = M.eval u ∧
        ∀ x, M.dom d.res x → b (M.eval u) x = x ∧ b x (M.eval u) = x)

def RuleSat (r : Rule) : Prop :=
  ∀ σ : String → M.α,
    (∀ x ∈ r.vars, ∃ s, r.sorts.lookup x = some s ∧ M.dom s (σ x)) →
    (∀ e ∈ r.eqs, M.evalP σ e.1 = M.evalP σ e.2) → M.evalP σ r.lhs = M.evalP σ r.rhs

def DeclSat : Decl → Prop
  | .axiom l r => M.eval l = M.eval r
  | .rules rs => ∀ r, some r ∈ rs → M.RuleSat r
  | .goal _ _ => True

/-- `M` satisfies the signatures and laws of `P`'s operators, interprets each
literal of a literal sort in that sort, and satisfies every command of `P`
that starts before offset `p`. -/
def Models (P : Program) (p : Nat) : Prop :=
  (∀ d ∈ P.ops, M.OpTyped d ∧ M.OpSat d) ∧
  (∀ s v, s ∈ P.litSorts → M.dom s (M.lit s v)) ∧
  ∀ o d, (o, d) ∈ P.decls → o < p → M.DeclSat d

theorem Models.mono {M : Model} {P : Program} {p q : Nat} (h : M.Models P p) (hq : q ≤ p) :
    M.Models P q :=
  ⟨h.1, h.2.1, fun o d hd ho => h.2.2 o d hd (Nat.lt_of_lt_of_le ho hq)⟩

end Model

end SemperCheck

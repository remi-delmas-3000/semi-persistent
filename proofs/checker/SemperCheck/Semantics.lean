import SemperCheck.Syntax

/-!
# Models of a program

A model interprets every operator as a function on one carrier and every
literal as an element. It satisfies an operator's laws when the operator's
applications fold an associative binary operation (commutative for `ac` and
`aci`, idempotent for `aci`, with the declared identity as its unit), or when
a `comm` operator is symmetric in its two arguments. It satisfies the program
up to offset `p` when it satisfies every operator's laws and every `union` and
rule whose command starts before `p`. The soundness theorem (`Sound.lean`)
states that a `check-eq` at offset `p` holds in every such model.

The definitions in this file and in `Syntax.lean` are the statement of the
soundness theorem; the parser (`Parse.lean`) is the other trusted part.
-/

namespace SemperCheck

structure Model where
  α : Type
  app : String → List α → α
  lit : String → α

namespace Model

variable (M : Model)

def eval : Term → M.α
  | .lit v => M.lit v
  | .app f args => M.app f (args.map eval)

def evalP (σ : String → M.α) : Pat → M.α
  | .var x => σ x
  | .lit v => M.lit v
  | .app f args => M.app f (args.map (evalP σ))

/-- The laws of operator `d`. -/
def OpSat (d : OpDecl) : Prop :=
  match d.kind with
  | .plain => True
  | .comm => ∀ x y, M.app d.name [x, y] = M.app d.name [y, x]
  | k => ∃ b : M.α → M.α → M.α,
      (∀ x y z, b (b x y) z = b x (b y z)) ∧
      (∀ x xs, M.app d.name (x :: xs) = xs.foldl b x) ∧
      ((k = .ac ∨ k = .aci) → ∀ x y, b x y = b y x) ∧
      (k = .aci → ∀ x, b x x = x) ∧
      (∀ u, d.unit = some u → ∀ x, b (M.eval u) x = x ∧ b x (M.eval u) = x)

def RuleSat (r : Rule) : Prop :=
  ∀ σ : String → M.α,
    (∀ e ∈ r.eqs, M.evalP σ e.1 = M.evalP σ e.2) → M.evalP σ r.lhs = M.evalP σ r.rhs

def DeclSat : Decl → Prop
  | .axiom l r => M.eval l = M.eval r
  | .rules rs => ∀ r ∈ rs, M.RuleSat r
  | .goal _ _ => True

/-- `M` satisfies the operator laws of `P` and every command of `P` that
starts before offset `p`. -/
def Models (P : Program) (p : Nat) : Prop :=
  (∀ d ∈ P.ops, M.OpSat d) ∧ ∀ o d, (o, d) ∈ P.decls → o < p → M.DeclSat d

theorem Models.mono {M : Model} {P : Program} {p q : Nat} (h : M.Models P p) (hq : q ≤ p) :
    M.Models P q :=
  ⟨h.1, fun o d hd ho => h.2 o d hd (Nat.lt_of_lt_of_le ho hq)⟩

end Model

end SemperCheck

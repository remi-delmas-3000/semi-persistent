import SemperCheck.Syntax
import SemperCheck.Prim
import SemperCheck.Seq

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
application; with `:inverse g`, `g` gives inverses for it; with `:nilpotent n`,
`n` copies of an element make the unit; with `:cancellative`, it cancels); a `comm` operator is symmetric on well-sorted arguments; a rule
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
  | .napp f args ks =>
    M.app f (((args.map eval).zip ks).flatMap fun vk => List.replicate vk.2 vk.1)

mutual

/-- The value of a pattern under an assignment `σ` of its variables, an
assignment `ρ` of its rest variables to lists of elements, and an assignment
`μ` of its multiplicity variables to counts. A rest variable and a repeated
argument are no terms by themselves: they only contribute arguments
(`evalArgs`). -/
def evalP (σ : String → M.α) (ρ : String → List M.α) (μ : String → Nat) : Pat → M.α
  | .var x => σ x
  | .lit s v => M.lit s v
  | .rest _ => M.lit "" ""
  | .rep _ _ => M.lit "" ""
  | .times _ _ => M.lit "" ""
  | .count k => M.lit "i64" (toString (μ k))
  | .app f args => M.app f (evalArgs σ ρ μ args)

/-- The values of an argument list: a rest variable gives its whole list, a
repeated argument its value as many times as its count. -/
def evalArgs (σ : String → M.α) (ρ : String → List M.α) (μ : String → Nat) : List Pat → List M.α
  | [] => []
  | .rest x :: ps => ρ x ++ evalArgs σ ρ μ ps
  | .rep p k :: ps => List.replicate (μ k) (evalP σ ρ μ p) ++ evalArgs σ ρ μ ps
  | .times p n :: ps => List.replicate n (evalP σ ρ μ p) ++ evalArgs σ ρ μ ps
  | .var x :: ps => σ x :: evalArgs σ ρ μ ps
  | .lit s v :: ps => M.lit s v :: evalArgs σ ρ μ ps
  | .count k :: ps => M.lit "i64" (toString (μ k)) :: evalArgs σ ρ μ ps
  | .app f args :: ps => M.app f (evalArgs σ ρ μ args) :: evalArgs σ ρ μ ps

end

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
  -- `:assoc-left`: `f(x1, x2, .., xn)` is the left comb `b(..b(x1, x2).., xn)`.
  | .foldL => ∃ b : M.α → M.α → M.α,
      (∀ x y, M.dom d.res x → M.dom d.res y → M.dom d.res (b x y)) ∧
      (∀ x xs, M.dom d.res x → (∀ y ∈ xs, M.dom d.res y) →
        M.app d.name (x :: xs) = xs.foldl b x)
  -- `:assoc-right`: `f(x1, .., xn)` is the right comb `b(x1, ..b(xn-1, xn)..)`.
  | .foldR => ∃ b : M.α → M.α → M.α,
      (∀ x y, M.dom d.res x → M.dom d.res y → M.dom d.res (b x y)) ∧
      (∀ x xs, M.dom d.res x → (∀ y ∈ xs, M.dom d.res y) →
        M.app d.name (xs ++ [x]) = xs.foldr b x)
  | k => ∃ b : M.α → M.α → M.α,
      (∀ x y, M.dom d.res x → M.dom d.res y → M.dom d.res (b x y)) ∧
      (∀ x y z, M.dom d.res x → M.dom d.res y → M.dom d.res z →
        b (b x y) z = b x (b y z)) ∧
      (∀ x xs, M.dom d.res x → (∀ y ∈ xs, M.dom d.res y) →
        M.app d.name (x :: xs) = xs.foldl b x) ∧
      ((k = .ac ∨ k = .aci) → ∀ x y, M.dom d.res x → M.dom d.res y → b x y = b y x) ∧
      (k = .aci → ∀ x, M.dom d.res x → b x x = x) ∧
      (∀ u, d.unit = some u → M.dom d.res (M.eval u) ∧ M.app d.name [] = M.eval u ∧
        ∀ x, M.dom d.res x → b (M.eval u) x = x ∧ b x (M.eval u) = x) ∧
      -- `:inverse g`, with the unit `u`: `g` sends an element to its inverse.
      (∀ g u, d.inverse = some g → d.unit = some u → ∀ x, M.dom d.res x →
        M.dom d.res (M.app g [x]) ∧ b x (M.app g [x]) = M.eval u) ∧
      -- `:nilpotent (n + 1)`, with the unit `u`: `n + 1` copies make the unit.
      (∀ n u, d.nilpotent = some (n + 1) → d.unit = some u → ∀ x, M.dom d.res x →
        (List.replicate n x).foldl b x = M.eval u) ∧
      -- `:cancellative`.
      (d.cancellative = true → ∀ x y z, M.dom d.res x → M.dom d.res y → M.dom d.res z →
        b x z = b y z → x = y)

def RuleSat (r : Rule) : Prop :=
  ∀ (σ : String → M.α) (ρ : String → List M.α) (μ : String → Nat),
    (∀ x ∈ r.vars, ∃ s, r.sorts.lookup x = some s ∧ M.dom s (σ x)) →
    (∀ x ∈ r.rests, ∃ s, r.sorts.lookup x = some s ∧ ∀ y ∈ ρ x, M.dom s y) →
    (∀ kn ∈ r.mults, kn.2 ≤ μ kn.1) →
    (∀ e ∈ r.eqs, M.evalP σ ρ μ e.1 = M.evalP σ ρ μ e.2) →
    M.evalP σ ρ μ r.lhs = M.evalP σ ρ μ r.rhs

/-- The value of a sequence rule's atom: `v` names the values. -/
def evA (v : Nat → M.α) : SAtom → M.α
  | .node n => v n
  | .lit s t => M.lit s t

def evS (v : Nat → M.α) : STm → M.α
  | .atom a => M.evA v a
  | .app f args => M.app f (args.map (evS v))

/-- A sequence rule holds when the two terms it yields are equal, under every
binding and every valuation of the binding's atoms (`Seq.lean`). -/
def SeqSat (r : SeqRule) : Prop :=
  ∀ (v : Nat → M.α) (B : SBind) (L R : STm), seqApply r B = some (L, R) → M.evS v L = M.evS v R

def DeclSat : Decl → Prop
  | .axiom l r => M.eval l = M.eval r
  | .rules rs => ∀ r, some r ∈ rs → M.RuleSat r
  | .seq rs => ∀ sr, some sr ∈ rs → M.SeqSat sr
  | .goal _ _ => True

/-- `M` satisfies the signatures and laws of `P`'s operators, interprets each
literal of a literal sort in that sort, satisfies every command of `P` that
starts before offset `p` and is in force there (no `pop` before `p` closed a
scope that holds it), and computes each primitive on literals as `primOk`
says. -/
def Models (P : Program) (p : Nat) : Prop :=
  (∀ d ∈ P.ops, M.OpTyped d ∧ M.OpSat d) ∧
  (∀ s v, s ∈ P.litSorts → M.dom s (M.lit s v)) ∧
  (∀ o d, (o, d) ∈ P.decls → o < p → P.active o p = true → M.DeclSat d) ∧
  -- A primitive applied to literals is the literal it computes (`Prim.lean`).
  ∀ f args out, primOk f args out = true →
    M.app f (args.map fun a => M.lit a.1 a.2) = M.lit out.1 out.2

/-- A command in force at `q` is in force at `p ≥ q`, when no scope that
holds `q` was closed before `p`. -/
theorem Program.active_of_stays {P : Program} {o q p : Nat} (ho : o < q)
    (ha : P.active o q = true) (hs : P.stays q p = true) : P.active o p = true := by
  unfold Program.active at ha ⊢
  unfold Program.stays at hs
  rw [List.all_eq_true] at ha hs ⊢
  intro se hse
  have h1 := ha se hse
  have h2 := hs se hse
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at h1 h2 ⊢
  omega

/-- The command at `o` is in force right after it. -/
theorem Program.active_succ (P : Program) (o : Nat) : P.active o (o + 1) = true := by
  unfold Program.active
  rw [List.all_eq_true]
  intro se _
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

theorem Models.mono {M : Model} {P : Program} {p q : Nat} (h : M.Models P p) (hq : q ≤ p)
    (hs : P.stays q p = true) : M.Models P q :=
  ⟨h.1, h.2.1, fun o d hd ho ha =>
    h.2.2.1 o d hd (Nat.lt_of_lt_of_le ho hq) (Program.active_of_stays ho ha hs), h.2.2.2⟩

end Model

end SemperCheck

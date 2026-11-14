/-!
# Folding a binary operation over a list

`lift b` extends `b` to `Option α` with `none` as a unit, so `fold b` of the
empty list is `none` and every list folds without a special case. The lemmas
give the laws the congruence check uses, for an operation whose laws hold on
the elements satisfying a predicate `p` (the elements of one sort) and lists
of such elements: a fold over a concatenation (from associativity),
invariance under permutation (commutativity), absorption of a repeated
element (idempotence), and removal of a unit.
-/

namespace SemperCheck

variable {α : Type} (b : α → α → α)

def lift : Option α → Option α → Option α
  | none, y => y
  | x, none => x
  | some x, some y => some (b x y)

def fold : List α → Option α
  | [] => none
  | x :: xs => lift b (some x) (fold xs)

/-- Folds a list of partial values. -/
def foldO : List (Option α) → Option α
  | [] => none
  | o :: os => lift b o (foldO os)

variable {b}

@[simp] theorem lift_none_left (y : Option α) : lift b none y = y := by cases y <;> rfl
@[simp] theorem lift_none_right (x : Option α) : lift b x none = x := by cases x <;> rfl
@[simp] theorem lift_some_some (x y : α) : lift b (some x) (some y) = some (b x y) := rfl

theorem foldO_map_some (l : List α) : foldO b (l.map some) = fold b l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [foldO, fold, ih]

/-! ## Laws relative to a predicate -/

variable {p : α → Prop}

/-- Every value the option holds satisfies `p`. -/
def OptP (p : α → Prop) (o : Option α) : Prop := ∀ x, o = some x → p x

theorem optP_none : OptP p none := fun _ h => by cases h

theorem optP_some {x : α} (h : p x) : OptP p (some x) := fun _ hy => by cases hy; exact h

theorem lift_closed (hc : ∀ x y, p x → p y → p (b x y)) {x y : Option α} (hx : OptP p x) (hy : OptP p y) : OptP p (lift b x y) := by
  cases x with
  | none => simpa using hy
  | some a =>
    cases y with
    | none => simpa using hx
    | some c => exact optP_some (hc a c (hx a rfl) (hy c rfl))

theorem fold_closed (hc : ∀ x y, p x → p y → p (b x y)) : ∀ (l : List α), (∀ x ∈ l, p x) → OptP p (fold b l)
  | [], _ => optP_none
  | x :: xs, h =>
    lift_closed hc (optP_some (h x (List.mem_cons_self ..)))
      (fold_closed hc xs fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem lift_assoc (hA : ∀ x y z, p x → p y → p z → b (b x y) z = b x (b y z)) {x y z : Option α} (hx : OptP p x) (hy : OptP p y) (hz : OptP p z) :
    lift b (lift b x y) z = lift b x (lift b y z) := by
  cases x <;> cases y <;> cases z <;> simp only [lift_none_left, lift_none_right, lift_some_some]
  exact congrArg some (hA _ _ _ (hx _ rfl) (hy _ rfl) (hz _ rfl))

theorem fold_append (hc : ∀ x y, p x → p y → p (b x y)) (hA : ∀ x y z, p x → p y → p z → b (b x y) z = b x (b y z)) (l m : List α) (hl : ∀ x ∈ l, p x) (hm : ∀ x ∈ m, p x) :
    fold b (l ++ m) = lift b (fold b l) (fold b m) := by
  induction l with
  | nil => simp [fold]
  | cons x xs ih =>
    have hxs : ∀ y ∈ xs, p y := fun y hy => hl y (List.mem_cons_of_mem _ hy)
    simp only [List.cons_append, fold]
    rw [ih hxs, lift_assoc hA (optP_some (hl x (List.mem_cons_self ..))) (fold_closed hc xs hxs)
      (fold_closed hc m hm)]

/-- An application of an associative operator is the fold of its arguments. -/
theorem fold_cons (hc : ∀ x y, p x → p y → p (b x y)) (hA : ∀ x y z, p x → p y → p z → b (b x y) z = b x (b y z)) : ∀ (x : α) (xs : List α), p x → (∀ y ∈ xs, p y) →
    fold b (x :: xs) = some (xs.foldl b x)
  | x, [], _, _ => by simp [fold]
  | x, y :: ys, hx, hxs => by
    have hy := hxs y (List.mem_cons_self ..)
    have hys : ∀ z ∈ ys, p z := fun z hz => hxs z (List.mem_cons_of_mem _ hz)
    simp only [List.foldl_cons]
    rw [← fold_cons hc hA (b x y) ys (hc _ _ hx hy) hys]
    simp only [fold]
    rw [← lift_assoc hA (optP_some hx) (optP_some hy) (fold_closed hc ys hys)]
    rfl

theorem fold_flatten (hc : ∀ x y, p x → p y → p (b x y)) (hA : ∀ x y z, p x → p y → p z → b (b x y) z = b x (b y z)) : ∀ (L : List (List α)), (∀ l ∈ L, ∀ x ∈ l, p x) →
    fold b L.flatten = foldO b (L.map (fold b))
  | [], _ => rfl
  | l :: ls, h => by
    have hls : ∀ l' ∈ ls, ∀ x ∈ l', p x := fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    rw [List.flatten_cons, fold_append hc hA l ls.flatten (h l (List.mem_cons_self ..))
      (fun x hx => by
        obtain ⟨l', hl', hx'⟩ := List.mem_flatten.1 hx
        exact hls l' hl' x hx'),
      fold_flatten hc hA ls hls]
    rfl

theorem lift_comm (hC : ∀ x y, p x → p y → b x y = b y x) {x y : Option α} (hx : OptP p x) (hy : OptP p y) :
    lift b x y = lift b y x := by
  cases x <;> cases y <;> simp only [lift_none_left, lift_none_right, lift_some_some]
  exact congrArg some (hC _ _ (hx _ rfl) (hy _ rfl))

theorem lift_left_comm (hA : ∀ x y z, p x → p y → p z → b (b x y) z = b x (b y z)) (hC : ∀ x y, p x → p y → b x y = b y x) {x y z : Option α} (hx : OptP p x) (hy : OptP p y) (hz : OptP p z) :
    lift b x (lift b y z) = lift b y (lift b x z) := by
  rw [← lift_assoc hA hx hy hz, lift_comm hC hx hy, lift_assoc hA hy hx hz]

theorem fold_perm (hc : ∀ x y, p x → p y → p (b x y)) (hA : ∀ x y z, p x → p y → p z → b (b x y) z = b x (b y z)) (hC : ∀ x y, p x → p y → b x y = b y x) {l m : List α} (h : l.Perm m) (hl : ∀ x ∈ l, p x) :
    fold b l = fold b m := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    simp only [fold]
    rw [ih fun y hy => hl y (List.mem_cons_of_mem _ hy)]
  | swap x y l =>
    simp only [fold]
    exact lift_left_comm hA hC (optP_some (hl y (List.mem_cons_self ..)))
      (optP_some (hl x (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      (fold_closed hc l fun z hz => hl z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)))
  | trans h1 _ ih1 ih2 => exact (ih1 hl).trans (ih2 fun x hx => hl x (h1.mem_iff.2 hx))

/-- An element already in the list is absorbed. -/
theorem fold_absorb (hc : ∀ x y, p x → p y → p (b x y)) (hA : ∀ x y z, p x → p y → p z → b (b x y) z = b x (b y z)) (hC : ∀ x y, p x → p y → b x y = b y x) (hI : ∀ x, p x → b x x = x) {l : List α} {y : α} (hy : y ∈ l) (hl : ∀ x ∈ l, p x) :
    fold b (y :: l) = fold b l := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hy
  have hp : (s ++ y :: t).Perm (y :: (s ++ t)) := List.perm_middle
  have hpy : p y := hl y hy
  have hst : ∀ x ∈ s ++ t, p x := fun x hx => hl x (hp.mem_iff.2 (List.mem_cons_of_mem _ hx))
  rw [fold_perm hc hA hC (List.Perm.cons y hp) (fun x hx => by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hpy
      · exact hl x hx),
    fold_perm hc hA hC hp hl]
  simp only [fold]
  rw [← lift_assoc hA (optP_some hpy) (optP_some hpy) (fold_closed hc _ hst)]
  simp [hI y hpy]

theorem fold_absorb_all (hc : ∀ x y, p x → p y → p (b x y)) (hA : ∀ x y z, p x → p y → p z → b (b x y) z = b x (b y z)) (hC : ∀ x y, p x → p y → b x y = b y x) (hI : ∀ x, p x → b x x = x) {l m : List α} (hm : ∀ y ∈ m, y ∈ l) (hl : ∀ x ∈ l, p x) :
    fold b (m ++ l) = fold b l := by
  induction m with
  | nil => rfl
  | cons y ys ih =>
    have hy : y ∈ ys ++ l := List.mem_append_right _ (hm y (List.mem_cons_self ..))
    have hys : ∀ z ∈ ys, z ∈ l := fun z hz => hm z (List.mem_cons_of_mem _ hz)
    rw [List.cons_append, fold_absorb hc hA hC hI hy (fun x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact hl x (hys x hx)
      · exact hl x hx)]
    exact ih hys

/-- Two lists with the same elements fold to the same value under an
associative, commutative and idempotent operation. -/
theorem fold_same_elems (hc : ∀ x y, p x → p y → p (b x y)) (hA : ∀ x y z, p x → p y → p z → b (b x y) z = b x (b y z)) (hC : ∀ x y, p x → p y → b x y = b y x) (hI : ∀ x, p x → b x x = x) {l m : List α} (hlm : ∀ y ∈ l, y ∈ m) (hml : ∀ y ∈ m, y ∈ l)
    (hl : ∀ x ∈ l, p x) : fold b l = fold b m := by
  have hm : ∀ x ∈ m, p x := fun x hx => hl x (hml x hx)
  rw [← fold_absorb_all hc hA hC hI hml hl, fold_perm hc hA hC List.perm_append_comm (fun x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact hm x hx
      · exact hl x hx),
    fold_absorb_all hc hA hC hI hlm hm]

/-- Removing the elements a map sends to a unit leaves the fold, read with
the unit for `none`, unchanged. -/
theorem fold_filter_unit_map {β : Type} {e : α} (hc : ∀ x y, p x → p y → p (b x y))
    (hl : ∀ x, p x → b e x = x) (hr : ∀ x, p x → b x e = x)
    (g : β → α) (q : β → Bool) (hq : ∀ x, q x = false → g x = e) :
    ∀ (l : List β), (∀ x ∈ l, p (g x)) →
      (fold b ((l.filter q).map g)).getD e = (fold b (l.map g)).getD e
  | [], _ => rfl
  | x :: xs, h => by
    have hxs : ∀ y ∈ xs, p (g y) := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have ih := fold_filter_unit_map hc hl hr g q hq xs hxs
    have hgx : p (g x) := h x (List.mem_cons_self ..)
    by_cases hqx : q x = true
    · simp only [List.filter_cons, hqx, ite_true, List.map_cons, fold]
      cases h1 : fold b ((xs.filter q).map g) <;> cases h2 : fold b (xs.map g) <;>
        simp only [h1, h2, Option.getD_none, Option.getD_some] at ih <;>
        simp only [lift_some_some, lift_none_right, Option.getD_some]
      · rw [← ih, hr _ hgx]
      · rw [ih, hr _ hgx]
      · rw [ih]
    · have hx := hq x (by simpa using hqx)
      simp only [List.filter_cons, hqx, List.map_cons, fold, hx]
      simp only [Bool.false_eq_true, ite_false] at ih ⊢
      cases h2 : fold b (xs.map g) with
      | none => simp only [h2, Option.getD_none] at ih; simp [ih]
      | some c =>
        have hpc : p c := fold_closed hc _ (by simpa using hxs) c h2
        simp only [h2, Option.getD_some] at ih
        simp [ih, hl c hpc]

end SemperCheck

/-!
# Folding a binary operation over a list

`lift b` extends `b` to `Option α` with `none` as a unit, so `fold b` of the
empty list is `none` and every list folds without a special case. The lemmas
give the laws the congruence check uses: a fold over a concatenation (from
associativity), invariance under permutation (commutativity), absorption of a
repeated element (idempotence), and removal of a unit.
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

theorem lift_assoc (hA : ∀ x y z, b (b x y) z = b x (b y z)) (x y z : Option α) :
    lift b (lift b x y) z = lift b x (lift b y z) := by
  cases x <;> cases y <;> cases z <;> simp [hA]

theorem lift_comm (hC : ∀ x y, b x y = b y x) (x y : Option α) : lift b x y = lift b y x := by
  cases x <;> cases y <;> simp [hC]

theorem lift_left_comm (hA : ∀ x y z, b (b x y) z = b x (b y z)) (hC : ∀ x y, b x y = b y x)
    (x y z : Option α) : lift b x (lift b y z) = lift b y (lift b x z) := by
  rw [← lift_assoc hA, lift_comm hC x y, lift_assoc hA]

theorem fold_append (hA : ∀ x y z, b (b x y) z = b x (b y z)) (l m : List α) :
    fold b (l ++ m) = lift b (fold b l) (fold b m) := by
  induction l with
  | nil => simp [fold]
  | cons x xs ih => simp [fold, ih, lift_assoc hA]

/-- An application of an associative operator is the fold of its arguments. -/
theorem fold_cons (hA : ∀ x y z, b (b x y) z = b x (b y z)) (x : α) (xs : List α) :
    fold b (x :: xs) = some (xs.foldl b x) := by
  induction xs generalizing x with
  | nil => simp [fold]
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rw [← ih (b x y)]
    simp only [fold]
    rw [← lift_assoc hA]
    rfl

theorem foldO_map_some (l : List α) : foldO b (l.map some) = fold b l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [foldO, fold, ih]

theorem fold_flatten (hA : ∀ x y z, b (b x y) z = b x (b y z)) (L : List (List α)) :
    fold b L.flatten = foldO b (L.map (fold b)) := by
  induction L with
  | nil => rfl
  | cons l ls ih => simp [foldO, fold_append hA, ih]

theorem fold_perm (hA : ∀ x y z, b (b x y) z = b x (b y z)) (hC : ∀ x y, b x y = b y x)
    {l m : List α} (h : l.Perm m) : fold b l = fold b m := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [fold, ih]
  | swap x y l => simp only [fold]; exact lift_left_comm hA hC _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- An element already in the list is absorbed. -/
theorem fold_absorb (hA : ∀ x y z, b (b x y) z = b x (b y z)) (hC : ∀ x y, b x y = b y x)
    (hI : ∀ x, b x x = x) {l : List α} {y : α} (hy : y ∈ l) :
    fold b (y :: l) = fold b l := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hy
  have hp : (s ++ y :: t).Perm (y :: (s ++ t)) := List.perm_middle
  rw [fold_perm hA hC (List.Perm.cons y hp), fold_perm hA hC hp]
  simp only [fold]
  rw [← lift_assoc hA]
  simp [hI]

theorem fold_absorb_all (hA : ∀ x y z, b (b x y) z = b x (b y z)) (hC : ∀ x y, b x y = b y x)
    (hI : ∀ x, b x x = x) {l m : List α} (hm : ∀ y ∈ m, y ∈ l) :
    fold b (m ++ l) = fold b l := by
  induction m with
  | nil => rfl
  | cons y ys ih =>
    have hy : y ∈ ys ++ l := List.mem_append_right _ (hm y (List.mem_cons_self ..))
    rw [List.cons_append, fold_absorb hA hC hI hy]
    exact ih fun z hz => hm z (List.mem_cons_of_mem _ hz)

/-- Two lists with the same elements fold to the same value under an
associative, commutative and idempotent operation. -/
theorem fold_same_elems (hA : ∀ x y z, b (b x y) z = b x (b y z)) (hC : ∀ x y, b x y = b y x)
    (hI : ∀ x, b x x = x) {l m : List α} (hlm : ∀ y ∈ l, y ∈ m) (hml : ∀ y ∈ m, y ∈ l) :
    fold b l = fold b m := by
  rw [← fold_absorb_all hA hC hI hml, fold_perm hA hC List.perm_append_comm,
    fold_absorb_all hA hC hI hlm]

/-- Removing elements equal to a unit leaves the fold, read with the unit for
`none`, unchanged. -/
theorem fold_filter_unit {e : α}
    (hl : ∀ x, b e x = x) (hr : ∀ x, b x e = x) (p : α → Bool) (hp : ∀ x, p x = false → x = e)
    (l : List α) : (fold b (l.filter p)).getD e = (fold b l).getD e := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : p x = true
    · simp only [List.filter_cons, h, ite_true, fold]
      cases h1 : fold b (xs.filter p) <;> cases h2 : fold b xs <;> simp_all
    · have hx := hp x (by simpa using h)
      subst hx
      simp only [List.filter_cons, h, fold]
      cases h2 : fold b xs <;> simp_all

/-- `fold_filter_unit` through a map: removing the elements the map sends to
the unit. -/
theorem fold_filter_unit_map {β : Type} {e : α} (hl : ∀ x, b e x = x) (hr : ∀ x, b x e = x)
    (g : β → α) (p : β → Bool) (hp : ∀ x, p x = false → g x = e) (l : List β) :
    (fold b ((l.filter p).map g)).getD e = (fold b (l.map g)).getD e := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : p x = true
    · simp only [List.filter_cons, h, ite_true, List.map_cons, fold]
      cases h1 : fold b ((xs.filter p).map g) <;> cases h2 : fold b (xs.map g) <;> simp_all
    · have hx := hp x (by simpa using h)
      simp only [List.filter_cons, h, List.map_cons, fold, hx]
      cases h2 : fold b (xs.map g) <;> simp_all

end SemperCheck

import SemperCheck.Kernel

/-!
# Counted children

A multiset node holds each child once with its count, as the engine's nodes
do. These lemmas say that the children repeated (`Ctx.spread`) are, up to
order, determined by the total count of each child.
-/

namespace SemperCheck

theorem count_replicate_nat (y c k : Nat) :
    (List.replicate k c).count y = if c = y then k else 0 := by
  rw [List.count_replicate]
  simp

theorem count_spread (y : Nat) : ∀ v : List (Nat × Nat), (Ctx.spread v).count y = total v y
  | [] => rfl
  | ck :: t => by
    have ih := count_spread y t
    unfold Ctx.spread at ih ⊢
    simp only [List.flatMap_cons, List.count_append, count_replicate_nat, ih, total,
      List.map_cons, List.sum_cons]

theorem total_scale (k y : Nat) : ∀ v : List (Nat × Nat), total (scaleC k v) y = total v y * k
  | [] => by simp [total, scaleC]
  | ck :: t => by
    have ih := total_scale k y t
    unfold total scaleC at ih ⊢
    simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]
    split <;> simp

theorem count_flatten_replicate (y : Nat) (l : List Nat) :
    ∀ k : Nat, ((List.replicate k l).flatten).count y = l.count y * k
  | 0 => by simp
  | k + 1 => by
    rw [List.replicate_succ, List.flatten_cons, List.count_append, count_flatten_replicate y l k,
      Nat.mul_succ, Nat.add_comm]

/-- Counts multiplied by `k` spread to `k` copies of the spread children, up
to order. -/
theorem spread_scale_perm (k : Nat) (v : List (Nat × Nat)) :
    (Ctx.spread (scaleC k v)).Perm ((List.replicate k (Ctx.spread v)).flatten) := by
  rw [List.perm_iff_count]
  intro y
  rw [count_spread, total_scale, count_flatten_replicate, count_spread]

/-- Two counted lists with the same total for every child spread to the same
children, up to order. -/
theorem spread_perm_of_total {l m : List (Nat × Nat)} (h : ∀ y, total l y = total m y) :
    (Ctx.spread l).Perm (Ctx.spread m) := by
  rw [List.perm_iff_count]
  intro y
  rw [count_spread, count_spread, h y]

theorem total_eq_zero {v : List (Nat × Nat)} {y : Nat} (h : ∀ yn ∈ v, yn.1 ≠ y) :
    total v y = 0 := by
  induction v with
  | nil => rfl
  | cons ck t ih =>
    unfold total at ih ⊢
    simp only [List.map_cons, List.sum_cons, ih fun yn hyn => h yn (List.mem_cons_of_mem _ hyn),
      if_neg (h ck (List.mem_cons_self ..))]

theorem mem_spread {v : List (Nat × Nat)} {y : Nat} (h : y ∈ Ctx.spread v) :
    ∃ yn ∈ v, yn.1 = y ∧ yn.2 ≠ 0 := by
  unfold Ctx.spread at h
  obtain ⟨yn, hyn, hy⟩ := List.mem_flatMap.1 h
  obtain ⟨hne, rfl⟩ := List.mem_replicate.1 hy
  exact ⟨yn, hyn, rfl, hne⟩

theorem mem_spread_of {v : List (Nat × Nat)} {yn : Nat × Nat} (h : yn ∈ v) (hne : yn.2 ≠ 0) :
    yn.1 ∈ Ctx.spread v := by
  unfold Ctx.spread
  exact List.mem_flatMap.2 ⟨yn, h, List.mem_replicate.2 ⟨hne, rfl⟩⟩

theorem spread_append (l m : List (Nat × Nat)) :
    Ctx.spread (l ++ m) = Ctx.spread l ++ Ctx.spread m := by
  unfold Ctx.spread
  exact List.flatMap_append ..

theorem spread_cons (c k : Nat) (t : List (Nat × Nat)) :
    Ctx.spread ((c, k) :: t) = List.replicate k c ++ Ctx.spread t := by
  unfold Ctx.spread
  rfl

/-- Filtering counted children by a test on the child filters their spread. -/
theorem spread_filter (q : Nat → Bool) : ∀ v : List (Nat × Nat),
    Ctx.spread (v.filter fun yn => q yn.1) = (Ctx.spread v).filter q
  | [] => rfl
  | (c, k) :: t => by
    have ih := spread_filter q t
    rw [spread_cons, List.filter_append, ← ih]
    cases hq : q c
    · rw [List.filter_cons_of_neg (by simpa using hq)]
      have : (List.replicate k c).filter q = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        rw [(List.mem_replicate.1 hx).2, hq]
        simp
      rw [this, List.nil_append]
    · rw [List.filter_cons_of_pos (by simpa using hq), spread_cons]
      have : (List.replicate k c).filter q = List.replicate k c := by
        rw [List.filter_eq_self]
        intro x hx
        rw [(List.mem_replicate.1 hx).2, hq]
      rw [this]

/-- Children of count zero spread to nothing. -/
theorem spread_filter_pos : ∀ v : List (Nat × Nat),
    Ctx.spread (v.filter fun yn => decide (yn.2 ≠ 0)) = Ctx.spread v
  | [] => rfl
  | (c, k) :: t => by
    have ih := spread_filter_pos t
    cases k with
    | zero =>
      rw [List.filter_cons_of_neg (by simp), ih, spread_cons]
      rfl
    | succ k =>
      rw [List.filter_cons_of_pos (by simp), spread_cons, spread_cons, ih]

theorem spread_ones : ∀ cs : List Nat, Ctx.spread (cs.map fun c => (c, 1)) = cs
  | [] => rfl
  | c :: t => by
    rw [List.map_cons, spread_cons, spread_ones t]
    rfl

theorem total_cons (c k : Nat) (t : List (Nat × Nat)) (z : Nat) :
    total ((c, k) :: t) z = (if c = z then k else 0) + total t z := by
  unfold total
  rfl

theorem total_addC (y k : Nat) : ∀ (v : List (Nat × Nat)) (z : Nat),
    total (addC y k v) z = total v z + (if y = z then k else 0)
  | [], z => by
    unfold addC
    rw [total_cons]
    unfold total
    simp
  | (c, j) :: t, z => by
    unfold addC
    split
    · rename_i h
      subst h
      rw [total_cons, total_cons]
      split <;> omega
    · rw [total_cons, total_cons, total_addC y k t z]
      omega

theorem total_foldl_addC : ∀ (v acc : List (Nat × Nat)) (z : Nat),
    total (v.foldl (fun acc yn => addC yn.1 yn.2 acc) acc) z = total acc z + total v z
  | [], acc, z => by
    unfold total
    simp
  | (c, k) :: t, acc, z => by
    rw [List.foldl_cons, total_foldl_addC t, total_addC, total_cons]
    show total acc z + (if c = z then k else 0) + total t z = _
    omega

theorem total_normC (v : List (Nat × Nat)) (z : Nat) : total (normC v) z = total v z := by
  unfold normC
  rw [total_foldl_addC]
  unfold total
  simp

end SemperCheck

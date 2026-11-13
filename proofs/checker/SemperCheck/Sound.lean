import SemperCheck.Semantics
import SemperCheck.Fold
import SemperCheck.Kernel

/-!
# Soundness of the checker

`goal_sound`: if every step of a certificate checks and step `s` is listed for
the `check-eq` at offset `o`, then that `check-eq` holds in every model of the
program's operator laws and of the commands before `o`.

The proof gives each node its value in a model (`nval`) and shows that each
step's conclusion holds between the values of its two nodes in every model of
the commands its derivation cites.
-/

namespace SemperCheck

open Model

variable (M : Model)

/-- The value of node `i` in `M`. -/
def nval (nodes : Array Node) (i : Nat) : M.α :=
  match nodes[i]? with
  | some (.lit v) => M.lit v
  | some (.app f cs) => M.app f (cs.map fun c => if _h : c < i then nval nodes c else M.lit "")
  | none => M.lit ""
termination_by i

variable {M}

/-! ## Lists -/

theorem mapM_some_map {α β γ : Type} {g : α → Option β} {F : α → γ} {G : β → γ} :
    ∀ (l : List α) (ids : List β), l.mapM g = some ids →
      (∀ a ∈ l, ∀ i, g a = some i → G i = F a) → ids.map G = l.map F
  | [], ids, h, _ => by simp_all
  | a :: as, ids, h, H => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨i, hi, is, his, rfl⟩ := h
    simp only [List.map_cons, H a (List.mem_cons_self ..) i hi,
      mapM_some_map as is his fun a' ha' => H a' (List.mem_cons_of_mem _ ha')]

theorem mapM_some_mem {α β : Type} {g : α → Option β} :
    ∀ (l : List α) (ids : List β), l.mapM g = some ids → ∀ y ∈ ids, ∃ x ∈ l, g x = some y
  | [], ids, h, y, hy => by simp_all
  | a :: as, ids, h, y, hy => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨i, hi, is, his, rfl⟩ := h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, List.mem_cons_self .., hi⟩
    · obtain ⟨x, hx, hgx⟩ := mapM_some_mem as is his y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hgx⟩

/-! ## Node values -/

theorem wf_child {nodes : Array Node} (hwf : wfNodes nodes = true) {i : Nat} {f : String}
    {cs : List Nat} (h : nodes[i]? = some (.app f cs)) : ∀ c ∈ cs, c < i := by
  have hi : i < nodes.size := by
    rcases Nat.lt_or_ge i nodes.size with hi | hi
    · exact hi
    · simp [Array.getElem?_eq_none hi] at h
  unfold wfNodes at hwf
  have := (List.all_eq_true.1 hwf) i (List.mem_range.2 hi)
  rw [h] at this
  intro c hc
  simpa using (List.all_eq_true.1 this) c hc

theorem nval_app {nodes : Array Node} (hwf : wfNodes nodes = true) {i : Nat} {f : String}
    {cs : List Nat} (h : nodes[i]? = some (.app f cs)) :
    nval M nodes i = M.app f (cs.map (nval M nodes)) := by
  rw [nval, h]
  simp only
  congr 1
  apply List.map_congr_left
  intro c hc
  simp [wf_child hwf h c hc]

theorem nval_lit {nodes : Array Node} {i : Nat} {v : String} (h : nodes[i]? = some (.lit v)) :
    nval M nodes i = M.lit v := by
  rw [nval, h]

namespace Ctx

variable {C : Ctx}

theorem lookup_some {n : Node} {i : Nat} (h : C.lookup n = some i) : C.nodes[i]? = some n := by
  unfold lookup at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

theorem intern_sound (hwf : wfNodes C.nodes = true) :
    ∀ (t : Term) (i : Nat), C.intern t = some i → nval M C.nodes i = M.eval t
  | .lit v, i, h => by
    rw [intern] at h
    rw [nval_lit (lookup_some h), Model.eval]
  | .app f args, i, h => by
    rw [intern, Option.bind_eq_some_iff] at h
    obtain ⟨ids, hids, hi⟩ := h
    rw [nval_app hwf (lookup_some hi), Model.eval]
    congr 1
    exact mapM_some_map args ids hids fun a _ j hj => intern_sound hwf a j hj

/-- The assignment `σ` names, through node values. -/
def sval (M : Model) (nodes : Array Node) (σ : List (String × Nat)) (x : String) : M.α :=
  match σ.lookup x with
  | some j => nval M nodes j
  | none => M.lit ""

theorem instP_sound (hwf : wfNodes C.nodes = true) (σ : List (String × Nat)) :
    ∀ (p : Pat) (i : Nat), C.instP σ p = some i →
      nval M C.nodes i = M.evalP (sval M C.nodes σ) p
  | .var x, i, h => by
    rw [instP] at h
    rw [Model.evalP, sval, h]
  | .lit v, i, h => by
    rw [instP] at h
    rw [nval_lit (lookup_some h), Model.evalP]
  | .app f ps, i, h => by
    rw [instP, Option.bind_eq_some_iff] at h
    obtain ⟨ids, hids, hi⟩ := h
    rw [nval_app hwf (lookup_some hi), Model.evalP]
    congr 1
    exact mapM_some_map ps ids hids fun a _ j hj => instP_sound hwf σ a j hj

/-! ## Flattened views -/

/-- The laws an `assoc`, `ac` or `aci` operator `f` has in `M` through `b`. -/
structure AssocLaws (M : Model) (f : String) (b : M.α → M.α → M.α) : Prop where
  assoc : ∀ x y z, b (b x y) z = b x (b y z)
  app : ∀ x xs, M.app f (x :: xs) = xs.foldl b x

theorem view_sound (hwf : wfNodes C.nodes = true) {f : String} {b : M.α → M.α → M.α}
    (L : AssocLaws M f b) : ∀ (x : Nat) (v : List Nat), C.view f x = some v →
      fold b (v.map (nval M C.nodes)) = some (nval M C.nodes x)
  | x, v, h => by
    rw [view] at h
    split at h
    · rename_i g cs hx
      split at h
      · subst_vars
        split at h
        · cases h
        · rename_i hne
          rw [Option.map_eq_some_iff] at h
          obtain ⟨vs, hvs, rfl⟩ := h
          rw [List.map_flatten, fold_flatten L.assoc, List.map_map]
          have hm := mapM_some_map (G := fun w => fold b (w.map (nval M C.nodes)))
            (F := fun c => some (nval M C.nodes c)) cs vs hvs (by
              intro c _ w hw
              split at hw
              · rename_i hc
                exact view_sound hwf L c w hw
              · cases hw)
          have hm' : vs.map (fold b ∘ List.map (nval M C.nodes)) = cs.map (some ∘ nval M C.nodes) := hm
          rw [hm', ← List.map_map, foldO_map_some, nval_app hwf hx]
          cases cs with
          | nil => simp at hne
          | cons c cs => rw [List.map_cons, fold_cons L.assoc, L.app]
      · cases h; simp [fold]
    · cases h; simp [fold]
termination_by x => x
decreasing_by assumption

theorem substOf_sound {prems : List (Nat × Nat)}
    (hp : ∀ p ∈ prems, nval M C.nodes p.1 = nval M C.nodes p.2) (y : Nat) :
    nval M C.nodes (substOf prems y) = nval M C.nodes y := by
  unfold substOf
  split
  · rename_i q hq
    have hmem := List.mem_of_find?_eq_some hq
    have hy : q.1 = y := by simpa using List.find?_some hq
    rw [← hy, hp q hmem]
  · rfl

theorem side_sound (hwf : wfNodes C.nodes = true) {f : String} {b : M.α → M.α → M.α}
    (L : AssocLaws M f b) {prems : List (Nat × Nat)}
    (hp : ∀ p ∈ prems, nval M C.nodes p.1 = nval M C.nodes p.2) {x : Nat} {l : List Nat}
    (h : C.side f prems x = some l) (D : M.α)
    (hD : ∀ u, C.unitOf f = some u →
      D = nval M C.nodes u ∧ (∀ y, b (nval M C.nodes u) y = y) ∧ ∀ y, b y (nval M C.nodes u) = y) :
    (fold b (l.map (nval M C.nodes))).getD D = nval M C.nodes x := by
  unfold side at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · cases h
    · rename_i ws hws
      cases h
      have hx := view_sound hwf L x v hv
      have hm := mapM_some_map (G := fun w => fold b (w.map (nval M C.nodes)))
        (F := fun y => some (nval M C.nodes y)) v ws hws (by
          intro y _ w hw
          rw [view_sound hwf L _ w hw, substOf_sound hp])
      have hflat : fold b (ws.flatten.map (nval M C.nodes)) = some (nval M C.nodes x) := by
        rw [List.map_flatten, fold_flatten L.assoc, List.map_map]
        have hm' : ws.map (fold b ∘ List.map (nval M C.nodes)) = v.map (some ∘ nval M C.nodes) := hm
        rw [hm', ← List.map_map, foldO_map_some, hx]
      cases hu : C.unitOf f with
      | none => simp only [dropUnit]; rw [hflat]; rfl
      | some u =>
        obtain ⟨rfl, hl, hr⟩ := hD u hu
        simp only [dropUnit]
        rw [fold_filter_unit_map hl hr _ _ (by intro y hy; simp at hy; rw [hy]), hflat]
        rfl

end Ctx

/-! ## Operator laws -/

theorem opDecl_spec {P : Program} {f : String} {d : OpDecl} (h : P.opDecl? f = some d) :
    d ∈ P.ops ∧ d.name = f := by
  unfold Program.opDecl? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem kind_spec {P : Program} {f : String} {k : Kind} (h : P.kind f = k) (hk : k ≠ .plain) :
    ∃ d, P.opDecl? f = some d ∧ d.kind = k := by
  unfold Program.kind at h
  split at h
  · rename_i d hd; exact ⟨d, hd, h⟩
  · exact absurd h.symm hk

/-- The laws of an `assoc`, `ac` or `aci` operator, read from the model. -/
theorem assoc_laws {d : OpDecl} (hs : M.OpSat d)
    (hk : d.kind = .assoc ∨ d.kind = .ac ∨ d.kind = .aci) :
    ∃ b : M.α → M.α → M.α, Ctx.AssocLaws M d.name b ∧
      ((d.kind = .ac ∨ d.kind = .aci) → ∀ x y, b x y = b y x) ∧
      (d.kind = .aci → ∀ x, b x x = x) ∧
      (∀ u, d.unit = some u → ∀ x, b (M.eval u) x = x ∧ b x (M.eval u) = x) := by
  unfold Model.OpSat at hs
  rcases hk with hk | hk | hk <;>
  · rw [hk] at hs
    obtain ⟨b, hA, hApp, hC, hI, hU⟩ := hs
    exact ⟨b, ⟨hA, hApp⟩, by rw [hk]; exact hC, by rw [hk]; exact hI, hU⟩

theorem comm_law {d : OpDecl} (hs : M.OpSat d) (hk : d.kind = .comm) :
    ∀ x y, M.app d.name [x, y] = M.app d.name [y, x] := by
  unfold Model.OpSat at hs
  rw [hk] at hs
  exact hs

namespace Ctx

variable {C : Ctx}

/-! ## Congruence -/

theorem pairsOk_sound {prems : List (Nat × Nat)}
    (hp : ∀ p ∈ prems, nval M C.nodes p.1 = nval M C.nodes p.2) :
    ∀ cs ds : List Nat, pairsOk prems cs ds = true →
      cs.map (nval M C.nodes) = ds.map (nval M C.nodes)
  | [], [], _ => rfl
  | c :: cs, d :: ds, h => by
    simp only [pairsOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    simp only [List.map_cons, pairsOk_sound hp cs ds h2, List.cons.injEq, and_true]
    rcases h1 with rfl | h1
    · rfl
    · exact hp (c, d) (by simpa using h1)
  | [], _ :: _, h => by simp [pairsOk] at h
  | _ :: _, [], h => by simp [pairsOk] at h

theorem congPlain_sound (hwf : wfNodes C.nodes = true) {f : String} {a b : Nat}
    {prems : List (Nat × Nat)} (hp : ∀ p ∈ prems, nval M C.nodes p.1 = nval M C.nodes p.2)
    (h : C.congPlain f a b prems = true) : nval M C.nodes a = nval M C.nodes b := by
  unfold congPlain at h
  split at h
  · rename_i g cs h' ds ha hb
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    rw [nval_app hwf ha, nval_app hwf hb, pairsOk_sound hp cs ds h]
  · cases h

theorem congComm_sound (hwf : wfNodes C.nodes = true) (hM : ∀ d ∈ C.P.ops, M.OpSat d)
    {f : String} (hk : C.P.kind f = .comm) {a b : Nat}
    {prems : List (Nat × Nat)} (hp : ∀ p ∈ prems, nval M C.nodes p.1 = nval M C.nodes p.2)
    (h : C.congComm f a b prems = true) : nval M C.nodes a = nval M C.nodes b := by
  obtain ⟨d, hd, hdk⟩ := kind_spec hk (by decide)
  obtain ⟨hmem, hname⟩ := opDecl_spec hd
  have hc := comm_law (hM d hmem) hdk
  rw [hname] at hc
  unfold congComm at h
  split at h
  · rename_i g c1 c2 h' d1 d2 ha hb
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    have := pairsOk_sound hp [c1, c2] [d2, d1] h
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at this
    rw [nval_app hwf ha, nval_app hwf hb]
    simp only [List.map_cons, List.map_nil, this.1, this.2]
    exact hc _ _
  · cases h

theorem congAssoc_sound (hwf : wfNodes C.nodes = true) (hM : ∀ d ∈ C.P.ops, M.OpSat d)
    {f : String} (hk : C.P.kind f = .assoc ∨ C.P.kind f = .ac ∨ C.P.kind f = .aci) {a b : Nat}
    {prems : List (Nat × Nat)} (hp : ∀ p ∈ prems, nval M C.nodes p.1 = nval M C.nodes p.2)
    (h : C.congAssoc f a b prems = true) : nval M C.nodes a = nval M C.nodes b := by
  obtain ⟨d, hd, hdk⟩ := kind_spec (k := C.P.kind f) rfl (by rcases hk with h | h | h <;> rw [h] <;> decide)
  obtain ⟨hmem, hname⟩ := opDecl_spec hd
  obtain ⟨op, L, hC, hI, hU⟩ := assoc_laws (hM d hmem) (by rw [hdk]; exact hk)
  rw [hname] at L
  let D : M.α := match C.unitOf f with
    | some u => nval M C.nodes u
    | none => M.lit ""
  have hD : ∀ u, C.unitOf f = some u → D = nval M C.nodes u ∧
      (∀ y, op (nval M C.nodes u) y = y) ∧ ∀ y, op y (nval M C.nodes u) = y := by
    intro u hu
    refine ⟨by simp only [D, hu], ?_⟩
    have hu' := hu
    unfold unitOf at hu'
    rw [hd] at hu'
    rw [Option.bind_eq_some_iff] at hu'
    obtain ⟨ut, hut, hint⟩ := hu'
    rw [intern_sound hwf ut u hint]
    exact ⟨fun y => (hU ut hut y).1, fun y => (hU ut hut y).2⟩
  unfold congAssoc at h
  split at h
  · rename_i l m hl hm
    rw [← side_sound hwf L hp hl D hD, ← side_sound hwf L hp hm D hD]
    congr 1
    rcases hk with hk | hk | hk <;> rw [hk] at h <;> simp only [sameBy] at h
    · rw [beq_iff_eq] at h; rw [h]
    · rw [← hdk] at hk
      exact fold_perm L.assoc (hC (Or.inl hk)) ((List.isPerm_iff.1 h).map _)
    · rw [← hdk] at hk
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      apply fold_same_elems L.assoc (hC (Or.inr hk)) (hI hk)
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
        exact List.mem_map_of_mem (h.1 z hz)
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
        exact List.mem_map_of_mem (h.2 z hz)
  · cases h

theorem congOk_sound (hwf : wfNodes C.nodes = true) (hM : ∀ d ∈ C.P.ops, M.OpSat d)
    {f : String} {a b : Nat}
    {prems : List (Nat × Nat)} (hp : ∀ p ∈ prems, nval M C.nodes p.1 = nval M C.nodes p.2)
    (h : C.congOk f a b prems = true) : nval M C.nodes a = nval M C.nodes b := by
  unfold congOk at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact congPlain_sound hwf hp h
  · split at h
    · cases h
    · exact congComm_sound hwf hM (by assumption) hp h
    · rename_i hk1 hk2
      have hk : C.P.kind f = .assoc ∨ C.P.kind f = .ac ∨ C.P.kind f = .aci := by
        cases hk : C.P.kind f <;> simp_all
      exact congAssoc_sound hwf hM hk hp h

/-! ## Steps -/

/-- The conclusion holds in every model of the commands it cites. -/
def Valid (M : Model) (C : Ctx) (c : Concl) : Prop :=
  M.Models C.P c.pos → nval M C.nodes c.a = nval M C.nodes c.b

def AllValid (M : Model) (C : Ctx) (acc : Array Concl) : Prop :=
  ∀ (s : Nat) (c : Concl), acc[s]? = some c → Valid M C c

theorem foldl_max_ge : ∀ (cs : List Concl) (init : Nat),
    init ≤ cs.foldl (fun m c => max m c.pos) init ∧
      ∀ c ∈ cs, c.pos ≤ cs.foldl (fun m c => max m c.pos) init
  | [], init => ⟨Nat.le_refl _, by simp⟩
  | c :: cs, init => by
    obtain ⟨h1, h2⟩ := foldl_max_ge cs (max init c.pos)
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, ?_⟩
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 c' hc'

theorem premConcls_sound {acc : Array Concl} (hacc : AllValid M C acc) {prems : List Nat}
    {ps : List (Nat × Nat)} {pos : Nat} (h : premConcls acc prems = some (ps, pos))
    (hM : M.Models C.P pos) : ∀ p ∈ ps, nval M C.nodes p.1 = nval M C.nodes p.2 := by
  unfold premConcls at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨cs, hcs, hps⟩ := h
  simp only [Prod.mk.injEq] at hps
  obtain ⟨rfl, rfl⟩ := hps
  intro p hp
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
  obtain ⟨s, _, hs⟩ := mapM_some_mem prems cs hcs c hc
  exact hacc s c hs (hM.mono ((foldl_max_ge cs 0).2 c hc))

theorem decl_mem {o : Nat} {d : Decl} (h : C.decl? o = some d) : (o, d) ∈ C.P.decls := by
  unfold decl? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨o', d'⟩, hf, rfl⟩ := h
  have ho : o' = o := by simpa using List.find?_some hf
  subst ho
  exact List.mem_of_find?_eq_some hf

theorem eqsOk_sound (hwf : wfNodes C.nodes = true) (σ : List (String × Nat)) :
    ∀ (es : List (Pat × Pat)) (ps : List (Nat × Nat)), C.eqsOk σ es ps = true →
      (∀ p ∈ ps, nval M C.nodes p.1 = nval M C.nodes p.2) →
      ∀ e ∈ es, M.evalP (sval M C.nodes σ) e.1 = M.evalP (sval M C.nodes σ) e.2
  | [], [], _, _ => by simp
  | (p, q) :: es, (x, y) :: ps, h, hps => by
    simp only [eqsOk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hp, hq⟩, h⟩ := h
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · rw [← instP_sound hwf σ p x hp, ← instP_sound hwf σ q y hq]
      exact hps (x, y) (List.mem_cons_self ..)
    · exact eqsOk_sound hwf σ es ps h (fun p hp => hps p (List.mem_cons_of_mem _ hp)) e he
  | [], _ :: _, h, _ => by simp [eqsOk] at h
  | _ :: _, [], h, _ => by simp [eqsOk] at h

theorem checkStep_sound (hwf : wfNodes C.nodes = true) {acc : Array Concl}
    (hacc : AllValid M C acc) {st : Step} {c : Concl} (h : C.checkStep acc st = some c) :
    Valid M C c := by
  intro hM
  cases st with
  | refl a => cases h; rfl
  | symm s =>
    simp only [checkStep, Option.map_eq_some_iff] at h
    obtain ⟨c', hc', rfl⟩ := h
    exact (hacc s c' hc' hM).symm
  | trans s t =>
    simp only [checkStep] at h
    split at h
    · rename_i c1 c2 h1 h2
      split at h
      · rename_i hb
        cases h
        have e1 := hacc s c1 h1 (hM.mono (Nat.le_max_left _ _))
        have e2 := hacc t c2 h2 (hM.mono (Nat.le_max_right _ _))
        simp only
        rw [e1, hb, e2]
      · cases h
    · cases h
  | «axiom» o a b =>
    simp only [checkStep] at h
    split at h
    · rename_i l r hd
      split at h
      · rename_i hab
        cases h
        have hs := hM.2 o _ (decl_mem hd) (Nat.lt_succ_self o)
        simp only [Model.DeclSat] at hs
        simp only
        rw [intern_sound hwf l a hab.1, intern_sound hwf r b hab.2, hs]
      · cases h
    · cases h
  | rule o j σ prems a b =>
    simp only [checkStep] at h
    split at h
    · rename_i rs hd
      split at h
      · rename_i r ps pos hr hps
        split at h
        · rename_i hok
          cases h
          obtain ⟨hl, hrr, heqs⟩ := hok
          have hs := hM.2 o _ (decl_mem hd) (Nat.lt_of_lt_of_le (Nat.lt_succ_self o) (Nat.le_max_left _ _))
          simp only [Model.DeclSat] at hs
          have hrule := hs r (List.mem_of_getElem? hr)
          have hpv := premConcls_sound hacc hps (hM.mono (Nat.le_max_right _ _))
          simp only
          rw [instP_sound hwf σ _ a hl, instP_sound hwf σ _ b hrr]
          exact hrule _ (eqsOk_sound hwf σ r.eqs ps heqs hpv)
        · cases h
      · cases h
    · cases h
  | cong f a b prems =>
    simp only [checkStep] at h
    split at h
    · rename_i ps pos hps
      split at h
      · rename_i hok
        cases h
        exact congOk_sound hwf hM.1 (premConcls_sound hacc hps hM) hok
      · cases h
    · cases h

theorem checkSteps_sound (hwf : wfNodes C.nodes = true) :
    ∀ (ss : List Step) (acc out : Array Concl), AllValid M C acc →
      C.checkSteps ss acc = some out → AllValid M C out
  | [], acc, out, hacc, h => by cases h; exact hacc
  | st :: ss, acc, out, hacc, h => by
    simp only [checkSteps] at h
    apply checkSteps_sound hwf ss _ out _ h
    intro s c' hs
    rw [Array.getElem?_push] at hs
    split at hs
    · cases hs
      cases hc : C.checkStep acc st with
      | some c => simp only [Option.getD_some]; exact checkStep_sound hwf hacc hc
      | none => intro _; rfl
    · exact hacc s c' hs

end Ctx

/-! ## The theorem -/

/-- **Soundness.** If every step of `cert` checks against `P` and the
certificate proves the `check-eq l r` at offset `o`, then `l = r` holds in
every model of the operator laws of `P` and of the commands of `P` before
`o`. -/
theorem goal_sound {P : Program} {cert : Cert} {C : Ctx} {acc : Array Concl}
    (hrun : runCert P cert = some (C, acc)) {o : Nat} {l r : Term}
    (hg : C.checkGoal acc cert.goals o l r = true) (M : Model) (hM : M.Models P o) :
    M.eval l = M.eval r := by
  unfold runCert at hrun
  split at hrun
  · rename_i hwf
    rw [Option.map_eq_some_iff] at hrun
    obtain ⟨acc', hsteps, hC⟩ := hrun
    simp only [Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl⟩ := hC
    have hwf' : wfNodes (mkCtx P cert).nodes = true := hwf
    have hall := Ctx.checkSteps_sound (M := M) hwf' _ #[] acc' (by intro s c hs; simp at hs) hsteps
    unfold Ctx.checkGoal at hg
    split at hg
    · rename_i o' s hf
      split at hg
      · rename_i c a b hc ha hb
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
        obtain ⟨⟨rfl, rfl⟩, hpos⟩ := hg
        rw [← Ctx.intern_sound hwf' l _ ha, ← Ctx.intern_sound hwf' r _ hb]
        exact hall s c hc (hM.mono hpos)
      · cases hg
    · cases hg
  · cases hrun

end SemperCheck

#print axioms SemperCheck.goal_sound

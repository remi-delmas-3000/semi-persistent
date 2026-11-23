import SemperCheck.Semantics
import SemperCheck.Fold
import SemperCheck.Kernel

/-!
# Soundness of the checker

`goal_sound`: if every step of a certificate checks and step `s` is listed for
the `check-eq` at offset `o`, then that `check-eq` holds in every model of the
program's operator signatures and laws and of the commands before `o`.

The proof gives each node its value in a model (`nval`), shows that a
well-sorted node's value is an element of its sort (`nval_dom`), and shows
that each step's conclusion holds between the values of its two nodes, which
are of one sort, in every model of the commands its derivation cites.
-/

namespace SemperCheck

open Model

variable (M : Model)

/-- The value of node `i` in `M`. -/
def nval (nodes : Array Node) (i : Nat) : M.α :=
  match nodes[i]? with
  | some (.lit s v) => M.lit s v
  | some (.app f cs) => M.app f (cs.map fun c => if _h : c < i then nval nodes c else M.lit "" "")
  | none => M.lit "" ""
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

theorem nval_lit {nodes : Array Node} {i : Nat} {s v : String} (h : nodes[i]? = some (.lit s v)) :
    nval M nodes i = M.lit s v := by
  rw [nval, h]

/-! ## Sorts -/

/-- `M` interprets the operators and the literals of `P` with their sorts and
laws. -/
def Typed (M : Model) (P : Program) : Prop :=
  (∀ d ∈ P.ops, M.OpTyped d ∧ M.OpSat d) ∧ (∀ s v, s ∈ P.litSorts → M.dom s (M.lit s v))

theorem Model.Models.typed {P : Program} {p : Nat} (h : M.Models P p) : Typed M P :=
  ⟨h.1, h.2.1⟩

theorem lt_size_of_some {nodes : Array Node} {i : Nat} {n : Node} (h : nodes[i]? = some n) :
    i < nodes.size := by
  rcases Nat.lt_or_ge i nodes.size with hi | hi
  · exact hi
  · simp [Array.getElem?_eq_none hi] at h

theorem wfSorts_lit {P : Program} {nodes : Array Node} (h : wfSorts P nodes = true) {i : Nat}
    {s v : String} (hn : nodes[i]? = some (.lit s v)) : s ∈ P.litSorts := by
  unfold wfSorts at h
  have := (List.all_eq_true.1 h) i (List.mem_range.2 (lt_size_of_some hn))
  rw [hn] at this
  simpa using this

theorem wfSorts_app {P : Program} {nodes : Array Node} (h : wfSorts P nodes = true) {i : Nat}
    {f : String} {cs : List Nat} (hn : nodes[i]? = some (.app f cs)) :
    ∃ d, P.opDecl? f = some d ∧
      (d.kind.isAssoc = true → (∀ c ∈ cs, nodeSort P nodes c = some d.res) ∧
        (cs ≠ [] ∨ d.unit.isSome = true)) ∧
      (d.kind.isAssoc = false → argsOk P nodes d.args cs = true) := by
  unfold wfSorts at h
  have := (List.all_eq_true.1 h) i (List.mem_range.2 (lt_size_of_some hn))
  rw [hn] at this
  simp only at this
  split at this
  · cases this
  · rename_i d hd
    refine ⟨d, hd, fun ha => ?_, fun ha => ?_⟩
    · rw [ha] at this; simp only [ite_true] at this
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.or_eq_true,
        Bool.not_eq_true', List.isEmpty_eq_false_iff] at this
      exact ⟨this.1, this.2⟩
    · rw [ha] at this
      simpa using this

theorem foldl_closed {α : Type} {p : α → Prop} {b : α → α → α}
    (hc : ∀ x y, p x → p y → p (b x y)) : ∀ (xs : List α) (x : α), p x → (∀ y ∈ xs, p y) →
      p (xs.foldl b x)
  | [], _, hx, _ => hx
  | y :: ys, x, hx, h =>
    foldl_closed hc ys (b x y) (hc _ _ hx (h y (List.mem_cons_self ..)))
      fun z hz => h z (List.mem_cons_of_mem _ hz)

theorem argsIn_of_argsOk {P : Program} {nodes : Array Node} :
    ∀ (ss : List String) (cs : List Nat), argsOk P nodes ss cs = true →
      (∀ c ∈ cs, ∀ s, nodeSort P nodes c = some s → M.dom s (nval M nodes c)) →
      M.ArgsIn ss (cs.map (nval M nodes))
  | [], [], _, _ => trivial
  | s :: ss, c :: cs, h, hd => by
    simp only [argsOk, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨hd c (List.mem_cons_self ..) s h.1,
      argsIn_of_argsOk ss cs h.2 fun c' hc' => hd c' (List.mem_cons_of_mem _ hc')⟩
  | [], _ :: _, h, _ => by simp [argsOk] at h
  | _ :: _, [], h, _ => by simp [argsOk] at h

theorem opDecl_spec {P : Program} {f : String} {d : OpDecl} (h : P.opDecl? f = some d) :
    d ∈ P.ops ∧ d.name = f := by
  unfold Program.opDecl? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- The laws of an `assoc`, `ac` or `aci` operator `f` of sort `s` in `M`
through `b`. -/
structure AssocLaws (M : Model) (f s : String) (b : M.α → M.α → M.α) : Prop where
  closed : ∀ x y, M.dom s x → M.dom s y → M.dom s (b x y)
  assoc : ∀ x y z, M.dom s x → M.dom s y → M.dom s z → b (b x y) z = b x (b y z)
  app : ∀ x xs, M.dom s x → (∀ y ∈ xs, M.dom s y) → M.app f (x :: xs) = xs.foldl b x

/-- The laws of an `assoc`, `ac` or `aci` operator, read from the model. -/
theorem assoc_laws {d : OpDecl} (hs : M.OpSat d) (hk : d.kind.isAssoc = true) :
    ∃ b : M.α → M.α → M.α, AssocLaws M d.name d.res b ∧
      ((d.kind = .ac ∨ d.kind = .aci) → ∀ x y, M.dom d.res x → M.dom d.res y → b x y = b y x) ∧
      (d.kind = .aci → ∀ x, M.dom d.res x → b x x = x) ∧
      (∀ u, d.unit = some u → M.dom d.res (M.eval u) ∧ M.app d.name [] = M.eval u ∧
        ∀ x, M.dom d.res x → b (M.eval u) x = x ∧ b x (M.eval u) = x) := by
  unfold Model.OpSat at hs
  cases hd : d.kind with
  | plain => simp [hd, Kind.isAssoc] at hk
  | comm => simp [hd, Kind.isAssoc] at hk
  | assoc | ac | aci =>
    rw [hd] at hs
    obtain ⟨b, hc, hA, hApp, hC, hI, hU, -⟩ := hs
    exact ⟨b, ⟨hc, hA, hApp⟩, hC, hI, hU⟩

/-- The laws of an `assoc`, `ac` or `aci` operator that the `inv`, `nil` and
`cancel` steps use, through one binary operation. -/
theorem assoc_laws_ext {d : OpDecl} (hs : M.OpSat d) (hk : d.kind.isAssoc = true) :
    ∃ b : M.α → M.α → M.α, AssocLaws M d.name d.res b ∧
      (∀ u, d.unit = some u → M.dom d.res (M.eval u) ∧ M.app d.name [] = M.eval u ∧
        ∀ x, M.dom d.res x → b (M.eval u) x = x ∧ b x (M.eval u) = x) ∧
      (∀ g u, d.inverse = some g → d.unit = some u → ∀ x, M.dom d.res x →
        M.dom d.res (M.app g [x]) ∧ b x (M.app g [x]) = M.eval u) ∧
      (∀ n u, d.nilpotent = some (n + 1) → d.unit = some u → ∀ x, M.dom d.res x →
        (List.replicate n x).foldl b x = M.eval u) ∧
      (d.cancellative = true → ∀ x y z, M.dom d.res x → M.dom d.res y → M.dom d.res z →
        b x z = b y z → x = y) := by
  unfold Model.OpSat at hs
  cases hd : d.kind with
  | plain => simp [hd, Kind.isAssoc] at hk
  | comm => simp [hd, Kind.isAssoc] at hk
  | assoc | ac | aci =>
    rw [hd] at hs
    obtain ⟨b, hc, hA, hApp, -, -, hU, hInv, hNil, hCan⟩ := hs
    exact ⟨b, ⟨hc, hA, hApp⟩, hU, hInv, hNil, hCan⟩

/-- A well-sorted node's value is an element of its sort. -/
theorem nval_dom {P : Program} {nodes : Array Node} (hwf : wfNodes nodes = true)
    (hws : wfSorts P nodes = true) (hT : Typed M P) :
    ∀ (i : Nat) (s : String), nodeSort P nodes i = some s → M.dom s (nval M nodes i) := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
  intro s hs
  unfold nodeSort at hs
  split at hs
  · rename_i s' v hn
    cases hs
    rw [nval_lit hn]
    exact hT.2 _ _ (wfSorts_lit hws hn)
  · rename_i f cs hn
    rw [Option.map_eq_some_iff] at hs
    obtain ⟨d, hd, rfl⟩ := hs
    obtain ⟨d', hd', hA, hF⟩ := wfSorts_app hws hn
    rw [hd] at hd'
    cases hd'
    obtain ⟨hmem, hname⟩ := opDecl_spec hd
    have hlt := wf_child hwf hn
    rw [nval_app hwf hn, ← hname]
    cases hk : d.kind.isAssoc
    · exact (hT.1 d hmem).1 hk _ (argsIn_of_argsOk _ _ (hF hk) fun c hc s' hs' => ih c (hlt c hc) s' hs')
    · obtain ⟨hcs, hne⟩ := hA hk
      obtain ⟨b, L, -, -, hU⟩ := assoc_laws (hT.1 d hmem).2 hk
      have hdc : ∀ c ∈ cs, M.dom d.res (nval M nodes c) := fun c hc => ih c (hlt c hc) _ (hcs c hc)
      cases cs with
      | nil =>
        cases hu : d.unit with
        | none => simp [hu] at hne
        | some u =>
          obtain ⟨hdu, happ, -⟩ := hU u hu
          simp only [List.map_nil, happ]
          exact hdu
      | cons c cs =>
        simp only [List.map_cons]
        rw [L.app _ _ (hdc c (List.mem_cons_self ..)) (by
          intro y hy
          obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hy
          exact hdc c' (List.mem_cons_of_mem _ hc'))]
        exact foldl_closed L.closed _ _ (hdc c (List.mem_cons_self ..)) (by
          intro y hy
          obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hy
          exact hdc c' (List.mem_cons_of_mem _ hc'))
  · cases hs

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
  | .lit s v, i, h => by
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
  | none => M.lit "" ""

/-- The assignment `ρ` names for the rest variables, through node values. -/
def rval (M : Model) (nodes : Array Node) (ρ : List (String × List Nat)) (x : String) :
    List M.α :=
  match ρ.lookup x with
  | some ns => ns.map (nval M nodes)
  | none => []

/-- The assignment `μ` names for the multiplicity variables. -/
def mval (μ : List (String × Nat)) (k : String) : Nat :=
  match μ.lookup k with
  | some n => n
  | none => 0

mutual

theorem instP_sound (hwf : wfNodes C.nodes = true) (σ : List (String × Nat))
    (ρ : List (String × List Nat)) (μ : List (String × Nat)) :
    ∀ (p : Pat) (i : Nat), C.instP σ ρ μ p = some i →
      nval M C.nodes i = M.evalP (sval M C.nodes σ) (rval M C.nodes ρ) (mval μ) p
  | .var x, i, h => by
    rw [instP] at h
    rw [Model.evalP, sval, h]
  | .lit s v, i, h => by
    rw [instP] at h
    rw [nval_lit (lookup_some h), Model.evalP]
  | .rest x, i, h => by
    rw [instP] at h
    cases h
  | .rep p k, i, h => by
    rw [instP] at h
    cases h
  | .times p n, i, h => by
    rw [instP] at h
    cases h
  | .count k, i, h => by
    rw [instP, Option.bind_eq_some_iff] at h
    obtain ⟨n, hn, h⟩ := h
    rw [nval_lit (lookup_some h), Model.evalP, mval, hn]
  | .app f ps, i, h => by
    rw [instP, Option.bind_eq_some_iff] at h
    obtain ⟨ids, hids, hi⟩ := h
    rw [nval_app hwf (lookup_some hi), Model.evalP, instArgs_sound hwf σ ρ μ ps ids hids]

theorem instArgs_sound (hwf : wfNodes C.nodes = true) (σ : List (String × Nat))
    (ρ : List (String × List Nat)) (μ : List (String × Nat)) :
    ∀ (ps : List Pat) (ids : List Nat), C.instArgs σ ρ μ ps = some ids →
      ids.map (nval M C.nodes) =
        M.evalArgs (sval M C.nodes σ) (rval M C.nodes ρ) (mval μ) ps
  | [], ids, h => by
    rw [instArgs] at h
    cases h
    rw [Model.evalArgs]
    rfl
  | .rest x :: ps, ids, h => by
    rw [instArgs, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    rw [Model.evalArgs, List.map_append, instArgs_sound hwf σ ρ μ ps t ht, rval, hr]
  | .rep p k :: ps, ids, h => by
    rw [instArgs, Option.bind_eq_some_iff] at h
    obtain ⟨n, hn, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨i, hi, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    rw [Model.evalArgs, List.map_append, List.map_replicate, instArgs_sound hwf σ ρ μ ps t ht,
      instP_sound hwf σ ρ μ p i hi, mval, hn]
  | .times p n :: ps, ids, h => by
    rw [instArgs, Option.bind_eq_some_iff] at h
    obtain ⟨i, hi, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    rw [Model.evalArgs, List.map_append, List.map_replicate, instArgs_sound hwf σ ρ μ ps t ht,
      instP_sound hwf σ ρ μ p i hi]
  | .count k :: ps, ids, h => by
    rw [instArgs, Option.bind_eq_some_iff] at h
    obtain ⟨i, hi, h⟩ := h
    rw [Option.bind_eq_some_iff] at hi
    obtain ⟨n, hn, hi⟩ := hi
    rw [Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    rw [Model.evalArgs, List.map_cons, instArgs_sound hwf σ ρ μ ps t ht,
      nval_lit (lookup_some hi), mval, hn]
  | .var x :: ps, ids, h => by
    rw [instArgs, Option.bind_eq_some_iff] at h
    obtain ⟨i, hi, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    rw [Model.evalArgs, List.map_cons, instArgs_sound hwf σ ρ μ ps t ht, sval, hi]
  | .lit s v :: ps, ids, h => by
    rw [instArgs, Option.bind_eq_some_iff] at h
    obtain ⟨i, hi, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    rw [Model.evalArgs, List.map_cons, instArgs_sound hwf σ ρ μ ps t ht, nval_lit (lookup_some hi)]
  | .app f as :: ps, ids, h => by
    rw [instArgs, Option.bind_eq_some_iff] at h
    obtain ⟨i, hi, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    rw [Option.bind_eq_some_iff] at hi
    obtain ⟨is, his, hi⟩ := hi
    rw [Model.evalArgs, List.map_cons, instArgs_sound hwf σ ρ μ ps t ht,
      nval_app hwf (lookup_some hi), instArgs_sound hwf σ ρ μ as is his]

end

/-! ## Flattened views -/

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

theorem substOf_sort {prems : List (Nat × Nat)}
    (hps : ∀ p ∈ prems, C.sortOf p.1 = C.sortOf p.2) (y : Nat) :
    C.sortOf (substOf prems y) = C.sortOf y := by
  unfold substOf
  split
  · rename_i q hq
    have hmem := List.mem_of_find?_eq_some hq
    have hy : q.1 = y := by simpa using List.find?_some hq
    rw [← hy, hps q hmem]
  · rfl

/-- The arguments of a flattened view are of the operator's sort and fold to
the node's value. -/
theorem view_sound (hwf : wfNodes C.nodes = true) (hws : wfSorts C.P C.nodes = true)
    (hT : Typed M C.P) {f : String} {d : OpDecl} (hd : C.P.opDecl? f = some d)
    (hk : d.kind.isAssoc = true) {b : M.α → M.α → M.α} (L : AssocLaws M f d.res b) :
    ∀ (x : Nat) (v : List Nat), C.view f x = some v → C.sortOf x = some d.res →
      (∀ y ∈ v, C.sortOf y = some d.res) ∧
        fold b (v.map (nval M C.nodes)) = some (nval M C.nodes x)
  | x, v, h, hx => by
    have hdom : ∀ c, C.sortOf c = some d.res → M.dom d.res (nval M C.nodes c) :=
      fun c hc => nval_dom hwf hws hT c _ hc
    rw [view] at h
    split at h
    · rename_i g cs hn
      split at h
      · rename_i hgf
        subst hgf
        split at h
        · cases h
        · rename_i hne
          rw [Option.map_eq_some_iff] at h
          obtain ⟨vs, hvs, rfl⟩ := h
          obtain ⟨d', hd', hA, -⟩ := wfSorts_app hws hn
          rw [hd] at hd'
          cases hd'
          have hcs := (hA hk).1
          have hrec : ∀ c ∈ cs, ∀ w, (if _h : c < x then C.view g c else none) = some w →
              (∀ y ∈ w, C.sortOf y = some d.res) ∧
                fold b (w.map (nval M C.nodes)) = some (nval M C.nodes c) := by
            intro c hc w hw
            split at hw
            · exact view_sound hwf hws hT hd hk L c w hw (hcs c hc)
            · cases hw
          have hsorts : ∀ y ∈ vs.flatten, C.sortOf y = some d.res := by
            intro y hy
            obtain ⟨w, hw, hyw⟩ := List.mem_flatten.1 hy
            obtain ⟨c, hc, hcw⟩ := mapM_some_mem cs vs hvs w hw
            exact (hrec c hc w hcw).1 y hyw
          refine ⟨hsorts, ?_⟩
          rw [List.map_flatten, fold_flatten L.closed L.assoc _ (by
            intro l hl y hy
            obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hl
            obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
            exact hdom z (hsorts z (List.mem_flatten.2 ⟨w, hw, hz⟩))), List.map_map]
          have hm := mapM_some_map (G := fun w => fold b (w.map (nval M C.nodes)))
            (F := fun c => some (nval M C.nodes c)) cs vs hvs (fun c hc w hw => (hrec c hc w hw).2)
          have hm' : vs.map (fold b ∘ List.map (nval M C.nodes)) =
              cs.map (some ∘ nval M C.nodes) := hm
          rw [hm', ← List.map_map, foldO_map_some, nval_app hwf hn]
          cases cs with
          | nil => simp at hne
          | cons c cs =>
            have hdc : ∀ c' ∈ c :: cs, M.dom d.res (nval M C.nodes c') :=
              fun c' hc' => hdom c' (hcs c' hc')
            have htail : ∀ y ∈ cs.map (nval M C.nodes), M.dom d.res y := by
              intro y hy
              obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hy
              exact hdc c' (List.mem_cons_of_mem _ hc')
            rw [List.map_cons, fold_cons L.closed L.assoc _ _ (hdc c (List.mem_cons_self ..)) htail,
              L.app _ _ (hdc c (List.mem_cons_self ..)) htail]
      · cases h
        exact ⟨by simpa using hx, by simp [fold]⟩
    · cases h
      exact ⟨by simpa using hx, by simp [fold]⟩
termination_by x => x
decreasing_by assumption

theorem side_sound (hwf : wfNodes C.nodes = true) (hws : wfSorts C.P C.nodes = true)
    (hT : Typed M C.P) {f : String} {d : OpDecl} (hd : C.P.opDecl? f = some d)
    (hk : d.kind.isAssoc = true) {b : M.α → M.α → M.α} (L : AssocLaws M f d.res b)
    {prems : List (Nat × Nat)}
    (hp : ∀ p ∈ prems, nval M C.nodes p.1 = nval M C.nodes p.2)
    (hps : ∀ p ∈ prems, C.sortOf p.1 = C.sortOf p.2) {x : Nat} {l : List Nat}
    (h : C.side f prems x = some l) (hx : C.sortOf x = some d.res) (D : M.α)
    (hD : ∀ u, C.unitOf f = some u → D = nval M C.nodes u ∧
      (∀ y, M.dom d.res y → b (nval M C.nodes u) y = y) ∧
      ∀ y, M.dom d.res y → b y (nval M C.nodes u) = y) :
    (∀ y ∈ l, C.sortOf y = some d.res) ∧
      (fold b (l.map (nval M C.nodes))).getD D = nval M C.nodes x := by
  have hdom : ∀ c, C.sortOf c = some d.res → M.dom d.res (nval M C.nodes c) :=
    fun c hc => nval_dom hwf hws hT c _ hc
  unfold side at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · cases h
    · rename_i ws hws'
      cases h
      obtain ⟨hvs, hx'⟩ := view_sound hwf hws hT hd hk L x v hv hx
      have hrec : ∀ y ∈ v, ∀ w, C.view f (substOf prems y) = some w →
          (∀ z ∈ w, C.sortOf z = some d.res) ∧
            fold b (w.map (nval M C.nodes)) = some (nval M C.nodes y) := by
        intro y hy w hw
        obtain ⟨h1, h2⟩ := view_sound hwf hws hT hd hk L _ w hw
          (by rw [substOf_sort hps]; exact hvs y hy)
        exact ⟨h1, by rw [h2, substOf_sound hp]⟩
      have hsorts : ∀ z ∈ ws.flatten, C.sortOf z = some d.res := by
        intro z hz
        obtain ⟨w, hw, hzw⟩ := List.mem_flatten.1 hz
        obtain ⟨y, hy, hyw⟩ := mapM_some_mem v ws hws' w hw
        exact (hrec y hy w hyw).1 z hzw
      have hm := mapM_some_map (G := fun w => fold b (w.map (nval M C.nodes)))
        (F := fun y => some (nval M C.nodes y)) v ws hws' (fun y hy w hw => (hrec y hy w hw).2)
      have hflat : fold b (ws.flatten.map (nval M C.nodes)) = some (nval M C.nodes x) := by
        rw [List.map_flatten, fold_flatten L.closed L.assoc _ (by
          intro l hl y hy
          obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hl
          obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
          exact hdom z (hsorts z (List.mem_flatten.2 ⟨w, hw, hz⟩))), List.map_map]
        have hm' : ws.map (fold b ∘ List.map (nval M C.nodes)) = v.map (some ∘ nval M C.nodes) := hm
        rw [hm', ← List.map_map, foldO_map_some, hx']
      cases hu : C.unitOf f with
      | none =>
        simp only [dropUnit]
        exact ⟨hsorts, by rw [hflat]; rfl⟩
      | some u =>
        obtain ⟨rfl, hl, hr⟩ := hD u hu
        simp only [dropUnit]
        refine ⟨fun y hy => hsorts y (List.mem_filter.1 hy).1, ?_⟩
        rw [fold_filter_unit_map L.closed hl hr _ _ (by intro y hy; simp at hy; rw [hy]) _
          (fun y hy => hdom y (hsorts y hy)), hflat]
        rfl

end Ctx

/-! ## Operator laws -/

theorem kind_spec {P : Program} {f : String} {k : Kind} (h : P.kind f = k) (hk : k ≠ .plain) :
    ∃ d, P.opDecl? f = some d ∧ d.kind = k := by
  unfold Program.kind at h
  split at h
  · rename_i d hd; exact ⟨d, hd, h⟩
  · exact absurd h.symm hk

theorem comm_law {d : OpDecl} (hs : M.OpSat d) (hk : d.kind = .comm) :
    ∀ x y, M.ArgsIn d.args [x, y] → M.ArgsIn d.args [y, x] →
      M.app d.name [x, y] = M.app d.name [y, x] := by
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

theorem congComm_sound (hwf : wfNodes C.nodes = true) (hws : wfSorts C.P C.nodes = true)
    (hT : Typed M C.P) {f : String} (hk : C.P.kind f = .comm) {a b : Nat}
    {prems : List (Nat × Nat)} (hp : ∀ p ∈ prems, nval M C.nodes p.1 = nval M C.nodes p.2)
    (h : C.congComm f a b prems = true) : nval M C.nodes a = nval M C.nodes b := by
  obtain ⟨d, hd, hdk⟩ := kind_spec hk (by decide)
  obtain ⟨hmem, hname⟩ := opDecl_spec hd
  have hc := comm_law (hT.1 d hmem).2 hdk
  rw [hname] at hc
  have hna : d.kind.isAssoc = false := by rw [hdk]; rfl
  have hargs : ∀ {i : Nat} {e1 e2 : Nat}, C.nodes[i]? = some (.app f [e1, e2]) →
      M.ArgsIn d.args [nval M C.nodes e1, nval M C.nodes e2] := by
    intro i e1 e2 hi
    obtain ⟨d', hd', -, hF⟩ := wfSorts_app hws hi
    rw [hd] at hd'
    cases hd'
    exact argsIn_of_argsOk _ [e1, e2] (hF hna) fun c _ s hs => nval_dom hwf hws hT c s hs
  unfold congComm at h
  split at h
  · rename_i g c1 c2 h' d1 d2 ha hb
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    have := pairsOk_sound hp [c1, c2] [d2, d1] h
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at this
    rw [nval_app hwf ha, nval_app hwf hb]
    simp only [List.map_cons, List.map_nil, this.1, this.2]
    have ha' := hargs ha
    rw [this.1, this.2] at ha'
    exact hc _ _ ha' (hargs hb)
  · cases h

theorem congAssoc_sound (hwf : wfNodes C.nodes = true) (hws : wfSorts C.P C.nodes = true)
    (hT : Typed M C.P) {f : String} {a b : Nat} {prems : List (Nat × Nat)}
    (hp : ∀ p ∈ prems, nval M C.nodes p.1 = nval M C.nodes p.2)
    (hps : ∀ p ∈ prems, C.sortOf p.1 = C.sortOf p.2)
    (h : C.congAssoc f a b prems = true) : nval M C.nodes a = nval M C.nodes b := by
  unfold congAssoc at h
  split at h
  · rename_i d l m hd hl hm
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨ha, hb⟩, h⟩ := h
    obtain ⟨hmem, hname⟩ := opDecl_spec hd
    have hk : d.kind.isAssoc = true := by
      cases hdk : d.kind <;> rw [hdk] at h <;> simp_all [sameBy, Kind.isAssoc]
    obtain ⟨op, L, hC, hI, hU⟩ := assoc_laws (hT.1 d hmem).2 hk
    rw [hname] at L
    let D : M.α := match C.unitOf f with
      | some u => nval M C.nodes u
      | none => M.lit "" ""
    have hD : ∀ u, C.unitOf f = some u → D = nval M C.nodes u ∧
        (∀ y, M.dom d.res y → op (nval M C.nodes u) y = y) ∧
        ∀ y, M.dom d.res y → op y (nval M C.nodes u) = y := by
      intro u hu
      refine ⟨by simp only [D, hu], ?_⟩
      have hu' := hu
      unfold unitOf at hu'
      rw [hd, Option.bind_eq_some_iff] at hu'
      obtain ⟨ut, hut, hint⟩ := hu'
      rw [intern_sound hwf ut u hint]
      obtain ⟨-, -, hlaw⟩ := hU ut hut
      exact ⟨fun y hy => (hlaw y hy).1, fun y hy => (hlaw y hy).2⟩
    obtain ⟨hls, hla⟩ := side_sound hwf hws hT hd hk L hp hps hl ha D hD
    obtain ⟨-, hmb⟩ := side_sound hwf hws hT hd hk L hp hps hm hb D hD
    rw [← hla, ← hmb]
    congr 1
    have hdl : ∀ x ∈ l.map (nval M C.nodes), M.dom d.res x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact nval_dom hwf hws hT y _ (hls y hy)
    cases hdk : d.kind with
    | plain => rw [hdk] at h; simp [sameBy] at h
    | comm => rw [hdk] at h; simp [sameBy] at h
    | assoc => rw [hdk] at h; simp only [sameBy, beq_iff_eq] at h; rw [h]
    | ac =>
      rw [hdk] at h
      simp only [sameBy] at h
      exact fold_perm L.closed L.assoc (hC (Or.inl hdk)) ((List.isPerm_iff.1 h).map _) hdl
    | aci =>
      rw [hdk] at h
      simp only [sameBy, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      apply fold_same_elems L.closed L.assoc (hC (Or.inr hdk)) (hI hdk)
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
        exact List.mem_map_of_mem (h.1 z hz)
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
        exact List.mem_map_of_mem (h.2 z hz)
      · exact hdl
  · cases h

theorem congOk_sound (hwf : wfNodes C.nodes = true) (hws : wfSorts C.P C.nodes = true)
    (hT : Typed M C.P) {f : String} {a b : Nat} {prems : List (Nat × Nat)}
    (hp : ∀ p ∈ prems, nval M C.nodes p.1 = nval M C.nodes p.2)
    (hps : ∀ p ∈ prems, C.sortOf p.1 = C.sortOf p.2)
    (h : C.congOk f a b prems = true) : nval M C.nodes a = nval M C.nodes b := by
  unfold congOk at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact congPlain_sound hwf hp h
  · split at h
    · cases h
    · exact congComm_sound hwf hws hT (by assumption) hp h
    · exact congAssoc_sound hwf hws hT hp hps h

/-! ## Steps -/

/-- The unit's node has the unit's value. -/
theorem unitOf_sound (hwf : wfNodes C.nodes = true) {f : String} {d : OpDecl} {e : Nat}
    (hd : C.P.opDecl? f = some d) (h : C.unitOf f = some e) :
    ∃ u, d.unit = some u ∧ nval M C.nodes e = M.eval u := by
  unfold unitOf at h
  rw [hd] at h
  obtain ⟨u, hu, hint⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨u, hu, intern_sound hwf u e hint⟩

/-- `f(x, g(x))` is the unit. -/
theorem invOk_sound (hwf : wfNodes C.nodes = true) (hws : wfSorts C.P C.nodes = true)
    (hT : Typed M C.P) {f : String} {a x q e : Nat} (h : C.invOk f a x q e = true) :
    nval M C.nodes a = nval M C.nodes e := by
  unfold invOk at h
  cases hd : C.P.opDecl? f with
  | none => simp [hd] at h
  | some d =>
    rw [hd] at h
    cases hg : d.inverse with
    | none => simp [hg] at h
    | some g =>
      simp only [hg, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hk, hn⟩, hq⟩, hu⟩ := h
      obtain ⟨u, hdu, hev⟩ := unitOf_sound (M := M) hwf hd hu
      obtain ⟨hmem, hname⟩ := opDecl_spec hd
      obtain ⟨b, L, -, hInv, -, -⟩ := assoc_laws_ext (hT.1 d hmem).2 hk
      obtain ⟨d', hd', hA, -⟩ := wfSorts_app hws hn
      rw [hd] at hd'
      cases hd'
      have hx : M.dom d.res (nval M C.nodes x) :=
        nval_dom hwf hws hT x _ ((hA hk).1 x (by simp))
      obtain ⟨hgx, hlaw⟩ := hInv g u hg hdu _ hx
      rw [nval_app hwf hn, hev]
      simp only [List.map_cons, List.map_nil]
      rw [nval_app hwf hq]
      simp only [List.map_cons, List.map_nil]
      rw [← hname, L.app _ _ hx (by
        intro y hy
        rw [List.mem_singleton] at hy
        rw [hy]
        exact hgx)]
      simpa using hlaw

/-- `f` of `k + 1` copies of `x` is the unit. -/
theorem nilOk_sound (hwf : wfNodes C.nodes = true) (hws : wfSorts C.P C.nodes = true)
    (hT : Typed M C.P) {f : String} {a x k e : Nat} (h : C.nilOk f a x k e = true) :
    nval M C.nodes a = nval M C.nodes e := by
  unfold nilOk at h
  cases hd : C.P.opDecl? f with
  | none => simp [hd] at h
  | some d =>
    rw [hd] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hk, hn⟩, hnil⟩, hu⟩ := h
    obtain ⟨u, hdu, hev⟩ := unitOf_sound (M := M) hwf hd hu
    obtain ⟨hmem, hname⟩ := opDecl_spec hd
    obtain ⟨b, L, -, -, hNil, -⟩ := assoc_laws_ext (hT.1 d hmem).2 hk
    obtain ⟨d', hd', hA, -⟩ := wfSorts_app hws hn
    rw [hd] at hd'
    cases hd'
    have hx : M.dom d.res (nval M C.nodes x) :=
      nval_dom hwf hws hT x _ ((hA hk).1 x (by simp))
    rw [nval_app hwf hn, hev]
    simp only [List.map_cons, List.map_replicate]
    rw [← hname, L.app _ _ hx (by
      intro y hy
      rw [List.eq_of_mem_replicate hy]
      exact hx)]
    exact hNil k u hnil hdu _ hx

/-- `f()` is the unit. -/
theorem unitOk_sound (hwf : wfNodes C.nodes = true) (hT : Typed M C.P) {f : String} {a e : Nat}
    (h : C.unitOk f a e = true) : nval M C.nodes a = nval M C.nodes e := by
  unfold unitOk at h
  cases hd : C.P.opDecl? f with
  | none => simp [hd] at h
  | some d =>
    rw [hd] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hk, hn⟩, hu⟩ := h
    obtain ⟨u, hdu, hev⟩ := unitOf_sound (M := M) hwf hd hu
    obtain ⟨hmem, hname⟩ := opDecl_spec hd
    obtain ⟨b, -, hU, -, -, -⟩ := assoc_laws_ext (hT.1 d hmem).2 hk
    rw [nval_app hwf hn, hev]
    simp only [List.map_nil]
    rw [← hname]
    exact (hU u hdu).2.1

/-- From `f(a, z) = f(b, z)`, `a = b`. -/
theorem cancelOk_sound (hwf : wfNodes C.nodes = true) (hws : wfSorts C.P C.nodes = true)
    (hT : Typed M C.P) {f : String} {p q a b z : Nat} (h : C.cancelOk f p q a b z = true)
    (hpq : nval M C.nodes p = nval M C.nodes q) : nval M C.nodes a = nval M C.nodes b := by
  unfold cancelOk at h
  cases hd : C.P.opDecl? f with
  | none => simp [hd] at h
  | some d =>
    rw [hd] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨hk, hp⟩, hq⟩, hlaw⟩ := h
    obtain ⟨hmem, hname⟩ := opDecl_spec hd
    obtain ⟨b', L, hU, hInv, -, hCan⟩ := assoc_laws_ext (hT.1 d hmem).2 hk
    obtain ⟨d1, hd1, hA1, -⟩ := wfSorts_app hws hp
    rw [hd] at hd1
    cases hd1
    obtain ⟨d2, hd2, hA2, -⟩ := wfSorts_app hws hq
    rw [hd] at hd2
    cases hd2
    have ha : M.dom d.res (nval M C.nodes a) := nval_dom hwf hws hT a _ ((hA1 hk).1 a (by simp))
    have hz : M.dom d.res (nval M C.nodes z) := nval_dom hwf hws hT z _ ((hA1 hk).1 z (by simp))
    have hb : M.dom d.res (nval M C.nodes b) := nval_dom hwf hws hT b _ ((hA2 hk).1 b (by simp))
    rw [nval_app hwf hp, nval_app hwf hq] at hpq
    simp only [List.map_cons, List.map_nil] at hpq
    rw [← hname, L.app _ _ ha (by
        intro y hy
        rw [List.mem_singleton] at hy
        rw [hy]
        exact hz),
      L.app _ _ hb (by
        intro y hy
        rw [List.mem_singleton] at hy
        rw [hy]
        exact hz)] at hpq
    simp only [List.foldl_cons, List.foldl_nil] at hpq
    cases hlaw with
    | inl hc => exact hCan hc _ _ _ ha hb hz hpq
    | inr hgu =>
      obtain ⟨hgs, hus⟩ := hgu
      obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hgs
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hus
      obtain ⟨u, hdu, -⟩ := unitOf_sound (M := M) hwf hd he
      obtain ⟨hgz, hzz⟩ := hInv g u hg hdu _ hz
      have h2 : b' (b' (nval M C.nodes a) (nval M C.nodes z)) (M.app g [nval M C.nodes z]) =
          b' (b' (nval M C.nodes b) (nval M C.nodes z)) (M.app g [nval M C.nodes z]) := by rw [hpq]
      rw [L.assoc _ _ _ ha hz hgz, L.assoc _ _ _ hb hz hgz, hzz,
        ((hU u hdu).2.2 _ ha).2, ((hU u hdu).2.2 _ hb).2] at h2
      exact h2

/-- The conclusion holds in every model of the commands it cites. -/
def Valid (M : Model) (C : Ctx) (c : Concl) : Prop :=
  M.Models C.P c.pos → nval M C.nodes c.a = nval M C.nodes c.b

/-- Every conclusion holds and relates two nodes of one sort. -/
def AllValid (M : Model) (C : Ctx) (acc : Array Concl) : Prop :=
  ∀ (s : Nat) (c : Concl), acc[s]? = some c → Valid M C c ∧ C.sortOf c.a = C.sortOf c.b

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
    {ps : List (Nat × Nat)} {pos : Nat} (h : premConcls acc prems = some (ps, pos)) :
    (M.Models C.P pos → ∀ p ∈ ps, nval M C.nodes p.1 = nval M C.nodes p.2) ∧
      ∀ p ∈ ps, C.sortOf p.1 = C.sortOf p.2 := by
  unfold premConcls at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨cs, hcs, hps⟩ := h
  simp only [Prod.mk.injEq] at hps
  obtain ⟨rfl, rfl⟩ := hps
  refine ⟨fun hM p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
    obtain ⟨s, _, hs⟩ := mapM_some_mem prems cs hcs c hc
    exact (hacc s c hs).1 (hM.mono ((foldl_max_ge cs 0).2 c hc))
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
    obtain ⟨s, _, hs⟩ := mapM_some_mem prems cs hcs c hc
    exact (hacc s c hs).2

theorem decl_mem {o : Nat} {d : Decl} (h : C.decl? o = some d) : (o, d) ∈ C.P.decls := by
  unfold decl? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨o', d'⟩, hf, rfl⟩ := h
  have ho : o' = o := by simpa using List.find?_some hf
  subst ho
  exact List.mem_of_find?_eq_some hf

theorem eqsOk_sound (hwf : wfNodes C.nodes = true) (σ : List (String × Nat))
    (ρ : List (String × List Nat)) (μ : List (String × Nat)) :
    ∀ (es : List (Pat × Pat)) (ps : List (Nat × Nat)), C.eqsOk σ ρ μ es ps = true →
      (∀ p ∈ ps, nval M C.nodes p.1 = nval M C.nodes p.2) →
      ∀ e ∈ es, M.evalP (sval M C.nodes σ) (rval M C.nodes ρ) (mval μ) e.1 =
        M.evalP (sval M C.nodes σ) (rval M C.nodes ρ) (mval μ) e.2
  | [], [], _, _ => by simp
  | (p, q) :: es, (x, y) :: ps, h, hps => by
    simp only [eqsOk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hp, hq⟩, h⟩ := h
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · rw [← instP_sound hwf σ ρ μ p x hp, ← instP_sound hwf σ ρ μ q y hq]
      exact hps (x, y) (List.mem_cons_self ..)
    · exact eqsOk_sound hwf σ ρ μ es ps h (fun p hp => hps p (List.mem_cons_of_mem _ hp)) e he
  | [], _ :: _, h, _ => by simp [eqsOk] at h
  | _ :: _, [], h, _ => by simp [eqsOk] at h

theorem sortsOk_sound (hwf : wfNodes C.nodes = true) (hws : wfSorts C.P C.nodes = true)
    (hT : Typed M C.P) {σ : List (String × Nat)} {r : Rule} (h : C.sortsOk σ r = true) :
    ∀ x ∈ r.vars, ∃ s, r.sorts.lookup x = some s ∧ M.dom s (sval M C.nodes σ x) := by
  intro x hx
  unfold sortsOk at h
  have hx' := (List.all_eq_true.1 h) x hx
  split at hx'
  · rename_i n s hn hs
    refine ⟨s, hs, ?_⟩
    simp only [beq_iff_eq] at hx'
    unfold sval
    rw [hn]
    exact nval_dom hwf hws hT n s hx'
  · cases hx'

theorem multsOk_sound {μ : List (String × Nat)} {r : Rule} (h : multsOk μ r = true) :
    ∀ kn ∈ r.mults, kn.2 ≤ mval μ kn.1 := by
  intro kn hkn
  unfold multsOk at h
  have hk := (List.all_eq_true.1 h) kn hkn
  unfold mval
  split at hk
  · rename_i v hv
    rw [hv]
    exact of_decide_eq_true hk
  · cases hk

theorem restsOk_sound (hwf : wfNodes C.nodes = true) (hws : wfSorts C.P C.nodes = true)
    (hT : Typed M C.P) {ρ : List (String × List Nat)} {r : Rule} (h : C.restsOk ρ r = true) :
    ∀ x ∈ r.rests, ∃ s, r.sorts.lookup x = some s ∧ ∀ y ∈ rval M C.nodes ρ x, M.dom s y := by
  intro x hx
  unfold restsOk at h
  have hx' := (List.all_eq_true.1 h) x hx
  split at hx'
  · rename_i ns s hn hs
    refine ⟨s, hs, ?_⟩
    intro y hy
    unfold rval at hy
    rw [hn] at hy
    obtain ⟨n, hn', rfl⟩ := List.mem_map.1 hy
    have := (List.all_eq_true.1 hx') n hn'
    simp only [beq_iff_eq] at this
    exact nval_dom hwf hws hT n s this
  · cases hx'

theorem primStepOk_sound (hwf : wfNodes C.nodes = true) {p : Nat} (hM : M.Models C.P p)
    {f : String} {a e : Nat} (h : C.primStepOk f a e = true) :
    nval M C.nodes a = nval M C.nodes e := by
  unfold primStepOk at h
  split at h
  · rename_i g cs out ha he
    rw [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · rename_i args hargs
      unfold litOf at he
      split at he
      · rename_i s v hlit
        cases he
        rw [nval_app hwf ha, nval_lit hlit, ← hM.2.2.2 g args (s, v) h]
        congr 1
        refine (mapM_some_map cs args hargs ?_).symm
        intro c _ sv hc
        unfold litOf at hc
        split at hc
        · rename_i s' v' hlit'
          cases hc
          exact (nval_lit hlit').symm
        · cases hc
      · cases he
    · cases h
  · cases h

theorem inferStep_sound (hwf : wfNodes C.nodes = true) (hws : wfSorts C.P C.nodes = true)
    {acc : Array Concl} (hacc : AllValid M C acc) {st : Step} {c : Concl}
    (h : C.inferStep acc st = some c) : Valid M C c := by
  intro hM
  have hT := hM.typed
  cases st with
  | refl a => cases h; rfl
  | symm s =>
    simp only [inferStep, Option.map_eq_some_iff] at h
    obtain ⟨c', hc', rfl⟩ := h
    exact ((hacc s c' hc').1 hM).symm
  | trans s t =>
    simp only [inferStep] at h
    split at h
    · rename_i c1 c2 h1 h2
      split at h
      · rename_i hb
        cases h
        have e1 := (hacc s c1 h1).1 (hM.mono (Nat.le_max_left _ _))
        have e2 := (hacc t c2 h2).1 (hM.mono (Nat.le_max_right _ _))
        simp only
        rw [e1, hb, e2]
      · cases h
    · cases h
  | «axiom» o a b =>
    simp only [inferStep] at h
    split at h
    · rename_i l r hd
      split at h
      · rename_i hab
        cases h
        have hs := hM.2.2.1 o _ (decl_mem hd) (Nat.lt_succ_self o)
        simp only [Model.DeclSat] at hs
        simp only
        rw [intern_sound hwf l a hab.1, intern_sound hwf r b hab.2, hs]
      · cases h
    · cases h
  | rule o j σ ρ μ prems a b =>
    simp only [inferStep] at h
    split at h
    · rename_i rs hd
      split at h
      · rename_i r ps pos hr hps
        split at h
        · rename_i hok
          cases h
          obtain ⟨hl, hrr, heqs, hso, hro, hmu⟩ := hok
          have hs := hM.2.2.1 o _ (decl_mem hd)
            (Nat.lt_of_lt_of_le (Nat.lt_succ_self o) (Nat.le_max_left _ _))
          simp only [Model.DeclSat] at hs
          have hrule := hs r (List.mem_of_getElem? hr)
          have hpv := (premConcls_sound hacc hps).1 (hM.mono (Nat.le_max_right _ _))
          simp only
          rw [instP_sound hwf σ ρ μ _ a hl, instP_sound hwf σ ρ μ _ b hrr]
          exact hrule _ _ _ (sortsOk_sound hwf hws hT hso) (restsOk_sound hwf hws hT hro)
            (multsOk_sound hmu) (eqsOk_sound hwf σ ρ μ r.eqs ps heqs hpv)
        · cases h
      · cases h
    · cases h
  | cong f a b prems =>
    simp only [inferStep] at h
    split at h
    · rename_i ps pos hps
      split at h
      · rename_i hok
        cases h
        exact congOk_sound hwf hws hT ((premConcls_sound hacc hps).1 hM)
          (premConcls_sound hacc hps).2 hok
      · cases h
    · cases h
  | inv f a x q e =>
    simp only [inferStep] at h
    split at h
    · rename_i hok
      cases h
      exact invOk_sound hwf hws hT hok
    · cases h
  | nil f a x k e =>
    simp only [inferStep] at h
    split at h
    · rename_i hok
      cases h
      exact nilOk_sound hwf hws hT hok
    · cases h
  | unit f a e =>
    simp only [inferStep] at h
    split at h
    · rename_i hok
      cases h
      exact unitOk_sound hwf hT hok
    · cases h
  | prim f a e =>
    simp only [inferStep] at h
    split at h
    · rename_i hok
      cases h
      exact primStepOk_sound hwf hM hok
    · cases h
  | cancel f s a b z =>
    simp only [inferStep] at h
    split at h
    · rename_i c hc
      split at h
      · rename_i hok
        cases h
        exact cancelOk_sound hwf hws hT hok ((hacc s c hc).1 hM)
      · cases h
    · cases h

theorem checkStep_sound (hwf : wfNodes C.nodes = true) (hws : wfSorts C.P C.nodes = true)
    {acc : Array Concl} (hacc : AllValid M C acc) {st : Step} {c : Concl}
    (h : C.checkStep acc st = some c) : Valid M C c ∧ C.sortOf c.a = C.sortOf c.b := by
  unfold checkStep at h
  split at h
  · rename_i c' hc'
    split at h
    · rename_i hs
      cases h
      exact ⟨inferStep_sound hwf hws hacc hc', hs.1⟩
    · cases h
  · cases h

theorem checkSteps_sound (hwf : wfNodes C.nodes = true) (hws : wfSorts C.P C.nodes = true) :
    ∀ (ss : List Step) (acc out : Array Concl), AllValid M C acc →
      C.checkSteps ss acc = some out → AllValid M C out
  | [], acc, out, hacc, h => by cases h; exact hacc
  | st :: ss, acc, out, hacc, h => by
    simp only [checkSteps] at h
    apply checkSteps_sound hwf hws ss _ out _ h
    intro s c' hs
    rw [Array.getElem?_push] at hs
    split at hs
    · cases hs
      cases hc : C.checkStep acc st with
      | some c => simp only [Option.getD_some]; exact checkStep_sound hwf hws hacc hc
      | none => exact ⟨fun _ => rfl, rfl⟩
    · exact hacc s c' hs

end Ctx

/-! ## The theorem -/

/-- **Soundness.** If every step of `cert` checks against `P` and the
certificate proves the `check-eq l r` at offset `o`, then `l = r` holds in
every model of the operator signatures and laws of `P` and of the commands of
`P` before `o`. -/
theorem goal_sound {P : Program} {cert : Cert} {C : Ctx} {acc : Array Concl}
    (hrun : runCert P cert = some (C, acc)) {o : Nat} {l r : Term}
    (hg : C.checkGoal acc cert.goals o l r = true) (M : Model) (hM : M.Models P o) :
    M.eval l = M.eval r := by
  unfold runCert at hrun
  split at hrun
  · rename_i hw
    rw [Bool.and_eq_true] at hw
    rw [Option.map_eq_some_iff] at hrun
    obtain ⟨acc', hsteps, hC⟩ := hrun
    simp only [Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl⟩ := hC
    have hwf' : wfNodes (mkCtx P cert).nodes = true := hw.1
    have hws' : wfSorts (mkCtx P cert).P (mkCtx P cert).nodes = true := hw.2
    have hall := Ctx.checkSteps_sound (M := M) hwf' hws' _ #[] acc'
      (by intro s c hs; simp at hs) hsteps
    unfold Ctx.checkGoal at hg
    split at hg
    · rename_i o' s hf
      split at hg
      · rename_i c a b hc ha hb
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
        obtain ⟨⟨rfl, rfl⟩, hpos⟩ := hg
        rw [← Ctx.intern_sound hwf' l _ ha, ← Ctx.intern_sound hwf' r _ hb]
        exact (hall s c hc).1 (hM.mono hpos)
      · cases hg
    · cases hg
  · cases hrun

end SemperCheck

#print axioms SemperCheck.goal_sound

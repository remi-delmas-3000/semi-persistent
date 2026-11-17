import SemperCheck.Sound

/-!
# The replayer's checked state

`Core P` is the part of the replayer's state that a proved `check-eq` depends
on: the node table, the conclusions of the kernel steps checked so far, the
union-find over node ids with the step that proves each link, the classes at
each mark, and the `check-eq` proved.

A `Core P` carries its invariant (`Raw.Ok`): the table is well-formed and
well-sorted, every conclusion holds in every model of the commands it cites,
every link of the union-find (current or marked) is the conclusion of a
checked step, and every recorded `check-eq` holds in every
model of the commands before it. The only functions that build a `Core P` are
the ones in this file, and each proves that it keeps the invariant:

* `addNode` appends a well-sorted node whose children are in the table;
* `emit` checks one kernel step (`Ctx.checkStep`) against the conclusions so
  far and appends its conclusion;
* `link` points a node at a smaller one, given a checked step that concludes
  the two equal;
* `mark`, `restore` save and reinstate classes whose links are checked;
* `goal` records a `check-eq` that a checked step concludes.

The rest of the replayer (`Replay.lean`) decides which of these to call. It
cannot produce a `Core P` any other way, so no property of it is assumed.
-/

namespace SemperCheck

/-! ## The node table grows -/

/-- The sort condition `wfSorts` asks of one node. -/
def nodeOk (P : Program) (nodes : Array Node) : Node → Bool
  | .lit s _ => P.litSorts.contains s
  | .app f cs =>
    match P.opDecl? f with
    | none => false
    | some d =>
      if d.kind.isAssoc then
        cs.all (fun c => nodeSort P nodes c == some d.res) && (!cs.isEmpty || d.unit.isSome)
      else argsOk P nodes d.args cs

/-- The condition `wfNodes` asks of node `i`. -/
def kidsBelow (i : Nat) : Node → Bool
  | .app _ cs => cs.all (· < i)
  | .lit _ _ => true

theorem wfNodes_iff {nodes : Array Node} :
    wfNodes nodes = true ↔ ∀ (i : Nat) (n : Node), nodes[i]? = some n → kidsBelow i n = true := by
  unfold wfNodes
  rw [List.all_eq_true]
  constructor
  · intro h i n hn
    have hi := lt_size_of_some hn
    have := h i (List.mem_range.2 hi)
    rw [hn] at this
    cases n <;> simp_all [kidsBelow]
  · intro h i _
    cases hn : nodes[i]? with
    | none => rfl
    | some n =>
      have := h i n hn
      cases n <;> simp_all [kidsBelow]

theorem wfSorts_iff {P : Program} {nodes : Array Node} :
    wfSorts P nodes = true ↔ ∀ (i : Nat) (n : Node), nodes[i]? = some n → nodeOk P nodes n = true := by
  unfold wfSorts
  rw [List.all_eq_true]
  constructor
  · intro h i n hn
    have hi := lt_size_of_some hn
    have := h i (List.mem_range.2 hi)
    rw [hn] at this
    cases n with
    | lit s v => simpa [nodeOk] using this
    | app f cs =>
      simp only [nodeOk]
      simp only at this
      exact this
  · intro h i _
    cases hn : nodes[i]? with
    | none => rfl
    | some n =>
      have := h i n hn
      cases n with
      | lit s v => simpa [nodeOk] using this
      | app f cs =>
        simp only [nodeOk] at this
        simp only
        exact this

theorem getElem?_push_lt {α : Type} (a : Array α) (x : α) {i : Nat} (h : i < a.size) :
    (a.push x)[i]? = a[i]? := by
  rw [Array.getElem?_push]
  simp [Nat.ne_of_lt h]

theorem getElem?_push_some {α : Type} (a : Array α) (x y : α) {i : Nat} (h : a[i]? = some y) :
    (a.push x)[i]? = some y := by
  have hi : i < a.size := by
    rcases Nat.lt_or_ge i a.size with hi | hi
    · exact hi
    · simp [Array.getElem?_eq_none hi] at h
  rw [getElem?_push_lt a x hi, h]

theorem nodeSort_push {P : Program} (nodes : Array Node) (n : Node) {i : Nat}
    (h : i < nodes.size) : nodeSort P (nodes.push n) i = nodeSort P nodes i := by
  unfold nodeSort
  rw [getElem?_push_lt nodes n h]

theorem nodeSort_lt {P : Program} {nodes : Array Node} {i : Nat} {s : String}
    (h : nodeSort P nodes i = some s) : i < nodes.size := by
  rcases Nat.lt_or_ge i nodes.size with hi | hi
  · exact hi
  · simp [nodeSort, Array.getElem?_eq_none hi] at h

theorem nodeSort_push_some {P : Program} (nodes : Array Node) (n : Node) {i : Nat} {s : String}
    (h : nodeSort P nodes i = some s) : nodeSort P (nodes.push n) i = some s := by
  rw [nodeSort_push nodes n (nodeSort_lt h), h]

theorem argsOk_push {P : Program} (nodes : Array Node) (n : Node) :
    ∀ (ss : List String) (cs : List Nat), argsOk P nodes ss cs = true →
      argsOk P (nodes.push n) ss cs = true
  | [], [], _ => rfl
  | s :: ss, c :: cs, h => by
    simp only [argsOk, Bool.and_eq_true, beq_iff_eq] at h ⊢
    exact ⟨nodeSort_push_some nodes n h.1, argsOk_push nodes n ss cs h.2⟩
  | [], _ :: _, h => by simp [argsOk] at h
  | _ :: _, [], h => by simp [argsOk] at h

theorem nodeOk_push {P : Program} (nodes : Array Node) (n m : Node)
    (h : nodeOk P nodes m = true) : nodeOk P (nodes.push n) m = true := by
  cases m with
  | lit s v => exact h
  | app f cs =>
    simp only [nodeOk] at h ⊢
    split
    · rename_i hd; rw [hd] at h; cases h
    · rename_i d hd
      rw [hd] at h
      simp only at h
      split
      · rename_i hk
        rw [if_pos hk] at h
        rw [Bool.and_eq_true] at h ⊢
        refine ⟨?_, h.2⟩
        rw [List.all_eq_true] at h ⊢
        intro c hc
        have := h.1 c hc
        rw [beq_iff_eq] at this ⊢
        exact nodeSort_push_some nodes n this
      · rename_i hk
        rw [if_neg hk] at h
        exact argsOk_push nodes n _ _ h

theorem wfNodes_push {nodes : Array Node} {n : Node} (hwf : wfNodes nodes = true)
    (hn : kidsBelow nodes.size n = true) : wfNodes (nodes.push n) = true := by
  rw [wfNodes_iff] at hwf ⊢
  intro i m hm
  rw [Array.getElem?_push] at hm
  split at hm
  · rename_i hi
    cases hm
    rw [hi]; exact hn
  · exact hwf i m hm

theorem wfSorts_push {P : Program} {nodes : Array Node} {n : Node}
    (hws : wfSorts P nodes = true) (hn : nodeOk P nodes n = true) :
    wfSorts P (nodes.push n) = true := by
  rw [wfSorts_iff] at hws ⊢
  intro i m hm
  rw [Array.getElem?_push] at hm
  split at hm
  · cases hm
    exact nodeOk_push nodes n n hn
  · exact nodeOk_push nodes n m (hws i m hm)

theorem nval_push (M : Model) (nodes : Array Node) (n : Node) :
    ∀ i, i < nodes.size → nval M (nodes.push n) i = nval M nodes i := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    rw [nval]
    conv => rhs; rw [nval]
    rw [getElem?_push_lt nodes n hi]
    cases h : nodes[i]? with
    | none => rfl
    | some nd =>
      cases nd with
      | lit s v => rfl
      | app f cs =>
        simp only
        congr 1
        apply List.map_congr_left
        intro c _
        split
        · rename_i hc; exact ih c hc (Nat.lt_trans hc hi)
        · rfl

/-! ## Links -/

/-- The root of `i`'s class. A non-root's parent is a smaller id, so the walk
ends without a step count. -/
def find (parent : Array Nat) (i : Nat) : Nat :=
  match parent[i]? with
  | some p => if _h : p < i then find parent p else i
  | none => i
termination_by i

/-- `p` with the entries `p.size .. n - 1` added, each its own parent. -/
def grow (p : Array Nat) (n : Nat) : Array Nat :=
  if p.size < n then grow (p.push p.size) n else p
termination_by n - p.size

/-- `a` with `none` added up to size `n`. -/
def growNone (a : Array (Option Nat)) (n : Nat) : Array (Option Nat) :=
  if a.size < n then growNone (a.push none) n else a
termination_by n - a.size

theorem grow_get (p : Array Nat) (n : Nat) {i q : Nat} (h : (grow p n)[i]? = some q) :
    p[i]? = some q ∨ q = i := by
  induction p using grow.induct n with
  | case1 p hlt ih =>
    rw [grow, if_pos hlt] at h
    rcases ih h with h' | h'
    · rw [Array.getElem?_push] at h'
      split at h'
      · rename_i hi; cases h'; exact .inr hi.symm
      · exact .inl h'
    · exact .inr h'
  | case2 p hlt =>
    rw [grow, if_neg hlt] at h
    exact .inl h

theorem growNone_size (a : Array (Option Nat)) (n : Nat) : n ≤ (growNone a n).size := by
  induction a using growNone.induct n with
  | case1 a hlt ih => rw [growNone, if_pos hlt]; exact ih
  | case2 a hlt => rw [growNone, if_neg hlt]; exact Nat.le_of_not_lt hlt

theorem growNone_get (a : Array (Option Nat)) (n : Nat) {i : Nat} {v : Option Nat}
    (h : a[i]? = some v) : (growNone a n)[i]? = some v := by
  induction a using growNone.induct n with
  | case1 a hlt ih => rw [growNone, if_pos hlt]; exact ih (getElem?_push_some a none v h)
  | case2 a hlt => rw [growNone, if_neg hlt]; exact h

/-- Each node with a smaller parent is proved equal to it by a checked step. -/
def Links (acc : Array Concl) (parent : Array Nat) (proof : Array (Option Nat)) : Prop :=
  ∀ (i p : Nat), parent[i]? = some p → p < i →
    ∃ (s : Nat) (c : Concl), proof[i]? = some (some s) ∧ acc[s]? = some c ∧ c.a = i ∧ c.b = p

theorem Links.push {acc : Array Concl} {parent : Array Nat} {proof : Array (Option Nat)}
    (h : Links acc parent proof) (c : Concl) : Links (acc.push c) parent proof := by
  intro i p hp hlt
  obtain ⟨s, c', h1, h2, h3⟩ := h i p hp hlt
  exact ⟨s, c', h1, getElem?_push_some acc c c' h2, h3⟩

theorem Links.empty (acc : Array Concl) : Links acc #[] #[] := by
  intro i p hp
  simp at hp

/-! ## The state -/

structure Raw where
  nodes : Array Node := #[]
  index : Std.HashMap Node Nat := {}
  /-- The conclusion of each kernel step checked so far. -/
  acc : Array Concl := #[]
  parent : Array Nat := #[]
  /-- For a node with a smaller parent, the step that concludes the two equal. -/
  proof : Array (Option Nat) := #[]
  /-- The classes at each mark. -/
  snaps : List (Array Nat × Array (Option Nat)) := []
  /-- The `check-eq` proved: offset, left term, right term. -/
  goals : List (Nat × Term × Term) := []
  /-- The steps the kernel rejected. -/
  rejected : Nat := 0

namespace Raw

def ctx (P : Program) (r : Raw) : Ctx := { P, nodes := r.nodes, index := r.index }

structure Ok (P : Program) (r : Raw) : Prop where
  wf : wfNodes r.nodes = true
  ws : wfSorts P r.nodes = true
  valid : ∀ M : Model, Ctx.AllValid M (r.ctx P) r.acc
  bnd : ∀ (s : Nat) (c : Concl), r.acc[s]? = some c → c.a = c.b ∨ (c.a < r.nodes.size ∧ c.b < r.nodes.size)
  links : Links r.acc r.parent r.proof
  snaps : ∀ x ∈ r.snaps, Links r.acc x.1 x.2
  goals : ∀ g ∈ r.goals, ∀ M : Model, M.Models P g.1 → M.eval g.2.1 = M.eval g.2.2

theorem Ok.empty (P : Program) : Ok P {} where
  wf := by simp [wfNodes]
  ws := by simp [wfSorts]
  valid := by intro M s c h; simp at h
  bnd := by intro s c h; simp at h
  links := Links.empty _
  snaps := by intro x hx; cases hx
  goals := by intro g hg; cases hg

/-- Appends node `n`, if its children are in the table and it is well-sorted. -/
def addNode (P : Program) (r : Raw) (n : Node) : Raw × Option Nat :=
  if kidsBelow r.nodes.size n && nodeOk P r.nodes n then
    let t := r.nodes.size
    ({ r with nodes := r.nodes.push n, index := r.index.insert n t }, some t)
  else (r, none)

theorem valid_push {P : Program} {r : Raw} (h : Ok P r) (n : Node) (idx : Std.HashMap Node Nat)
    (M : Model) : Ctx.AllValid M { P, nodes := r.nodes.push n, index := idx } r.acc := by
  intro s c hc
  have hv := h.valid M s c hc
  rcases h.bnd s c hc with he | ⟨ha, hb⟩
  · refine ⟨fun _ => by rw [he], by rw [he]⟩
  · refine ⟨fun hM => ?_, ?_⟩
    · show nval M (r.nodes.push n) c.a = nval M (r.nodes.push n) c.b
      rw [nval_push M r.nodes n _ ha, nval_push M r.nodes n _ hb]
      exact hv.1 hM
    · show nodeSort P (r.nodes.push n) c.a = nodeSort P (r.nodes.push n) c.b
      rw [nodeSort_push r.nodes n ha, nodeSort_push r.nodes n hb]
      exact hv.2

theorem addNode_ok {P : Program} {r : Raw} (h : Ok P r) (n : Node) : Ok P (addNode P r n).1 := by
  unfold addNode
  split
  · rename_i hc
    rw [Bool.and_eq_true] at hc
    exact
      { wf := wfNodes_push h.wf hc.1
        ws := wfSorts_push h.ws hc.2
        valid := valid_push h n _
        bnd := by
          intro s c hs
          rcases h.bnd s c hs with he | ⟨ha, hb⟩
          · exact .inl he
          · refine .inr ⟨?_, ?_⟩ <;> simp only [Array.size_push] <;> omega
        links := h.links
        snaps := h.snaps
        goals := h.goals }
  · exact h

/-- Checks kernel step `st` and appends its conclusion; a step that does not
check is counted and concludes `0 = 0`. -/
def emit (P : Program) (r : Raw) (st : Step) : Raw :=
  match (r.ctx P).checkStep r.acc st with
  | some c => { r with acc := r.acc.push c }
  | none => { r with acc := r.acc.push Ctx.failed, rejected := r.rejected + 1 }

theorem push_ok {P : Program} {r : Raw} (h : Ok P r) (c : Concl)
    (hv : ∀ M : Model, Ctx.Valid M (r.ctx P) c ∧ (r.ctx P).sortOf c.a = (r.ctx P).sortOf c.b)
    (hb : c.a = c.b ∨ (c.a < r.nodes.size ∧ c.b < r.nodes.size)) (k : Nat) :
    Ok P { r with acc := r.acc.push c, rejected := k } where
  wf := h.wf
  ws := h.ws
  valid := by
    intro M s c' hs
    rw [Array.getElem?_push] at hs
    split at hs
    · cases hs; exact hv M
    · exact h.valid M s c' hs
  bnd := by
    intro s c' hs
    rw [Array.getElem?_push] at hs
    split at hs
    · cases hs; exact hb
    · exact h.bnd s c' hs
  links := h.links.push c
  snaps := fun x hx => (h.snaps x hx).push c
  goals := h.goals

theorem emit_ok {P : Program} {r : Raw} (h : Ok P r) (st : Step) : Ok P (emit P r st) := by
  unfold emit
  split
  · rename_i c hc
    refine push_ok h c (fun M => Ctx.checkStep_sound h.wf h.ws (h.valid M) hc) ?_ _
    unfold Ctx.checkStep at hc
    split at hc
    · split at hc
      · rename_i hs
        cases hc
        obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.1 hs.2
        have ha := nodeSort_lt hs'
        have hb : nodeSort P r.nodes _ = some s := hs.1 ▸ hs'
        exact .inr ⟨ha, nodeSort_lt hb⟩
      · cases hc
    · cases hc
  · exact push_ok h Ctx.failed (fun M => ⟨fun _ => rfl, rfl⟩) (.inl rfl) _

/-- Points `hi` at `lo`, when step `s` concludes `hi = lo` and `lo < hi`. -/
def link (r : Raw) (hi lo s : Nat) : Raw × Bool :=
  match r.acc[s]? with
  | some c =>
    if c.a = hi ∧ c.b = lo ∧ lo < hi then
      ({ r with parent := (grow r.parent (hi + 1)).setIfInBounds hi lo,
                proof := (growNone r.proof (hi + 1)).setIfInBounds hi (some s) }, true)
    else (r, false)
  | none => (r, false)

theorem link_ok {P : Program} {r : Raw} (h : Ok P r) (hi lo s : Nat) : Ok P (link r hi lo s).1 := by
  unfold link
  split
  · rename_i c hc
    split
    · rename_i hcond
      obtain ⟨ha, hb, hlt⟩ := hcond
      refine { h with links := ?_ }
      intro i p hp hpi
      simp only [Array.getElem?_setIfInBounds] at hp ⊢
      by_cases hih : hi = i
      · subst hih
        rw [if_pos rfl] at hp
        split at hp
        · cases hp
          refine ⟨s, c, ?_, hc, ha, hb⟩
          rw [if_pos rfl, if_pos (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (growNone_size _ _))]
        · cases hp
      · rw [if_neg hih] at hp
        rcases grow_get _ _ hp with hp' | hp'
        · obtain ⟨s', c', h1, h2⟩ := h.links i p hp' hpi
          exact ⟨s', c', by rw [if_neg hih]; exact growNone_get _ _ h1, h2⟩
        · omega
    · exact h
  · exact h

/-- Saves the classes as mark `d`, dropping the marks from `d` on. -/
def mark (r : Raw) (d : Nat) : Raw :=
  { r with snaps := (r.parent, r.proof) :: (r.snaps.reverse.take d).reverse }

theorem mem_keep {α : Type} {l : List α} {d : Nat} {x : α} (h : x ∈ (l.reverse.take d).reverse) :
    x ∈ l :=
  List.mem_reverse.1 (List.mem_of_mem_take (List.mem_reverse.1 h))

theorem mark_ok {P : Program} {r : Raw} (h : Ok P r) (d : Nat) : Ok P (mark r d) :=
  { h with
    snaps := by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h.links
      · exact h.snaps x (mem_keep hx) }

/-- Reinstates the classes of mark `d` and keeps the first `keep` marks. -/
def restore (r : Raw) (d keep : Nat) : Raw × Bool :=
  match r.snaps.reverse[d]? with
  | some (p, pf) =>
    ({ r with parent := p, proof := pf,
              snaps := (r.snaps.reverse.take keep).reverse }, true)
  | none => (r, false)

theorem restore_ok {P : Program} {r : Raw} (h : Ok P r) (d keep : Nat) :
    Ok P (restore r d keep).1 := by
  unfold restore
  split
  · rename_i p pf hs
    have hm : (p, pf) ∈ r.snaps := List.mem_reverse.1 (List.mem_of_getElem? hs)
    have hl := h.snaps _ hm
    exact { h with links := hl, snaps := fun x hx => h.snaps x (mem_keep hx) }
  · exact h

/-- Records the `check-eq l r` at offset `o`, when step `s` concludes it from
commands before `o`. -/
def goal (P : Program) (r : Raw) (o : Nat) (lhs rhs : Term) (s : Nat) : Raw × Bool :=
  if (r.ctx P).checkGoal r.acc [(o, s)] o lhs rhs then
    ({ r with goals := (o, lhs, rhs) :: r.goals }, true)
  else (r, false)

theorem goal_ok {P : Program} {r : Raw} (h : Ok P r) (o : Nat) (lhs rhs : Term) (s : Nat) :
    Ok P (goal P r o lhs rhs s).1 := by
  unfold goal
  split
  · rename_i hg
    refine { h with goals := ?_ }
    intro g hg' M hM
    rcases List.mem_cons.1 hg' with rfl | hg'
    · unfold Ctx.checkGoal at hg
      split at hg
      · rename_i o' s' hf
        split at hg
        · rename_i c a b hc ha hb
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
          obtain ⟨⟨rfl, rfl⟩, hpos⟩ := hg
          have hwf : wfNodes (r.ctx P).nodes = true := h.wf
          show M.eval lhs = M.eval rhs
          rw [← Ctx.intern_sound hwf lhs _ ha, ← Ctx.intern_sound hwf rhs _ hb]
          exact (h.valid M s' c hc).1 (hM.mono hpos)
        · cases hg
      · cases hg
    · exact h.goals g hg' M hM
  · exact h

end Raw

/-- The replayer's checked state for program `P`. -/
def Core (P : Program) : Type := { r : Raw // r.Ok P }

namespace Core

variable {P : Program}

def new (P : Program) : Core P := ⟨{}, Raw.Ok.empty P⟩

instance : Inhabited (Core P) := ⟨new P⟩

@[inline] def nodes (c : Core P) : Array Node := c.1.nodes
@[inline] def index (c : Core P) : Std.HashMap Node Nat := c.1.index
@[inline] def acc (c : Core P) : Array Concl := c.1.acc
@[inline] def parent (c : Core P) : Array Nat := c.1.parent
@[inline] def proof (c : Core P) : Array (Option Nat) := c.1.proof
@[inline] def goals (c : Core P) : List (Nat × Term × Term) := c.1.goals
@[inline] def rejected (c : Core P) : Nat := c.1.rejected

def addNode (c : Core P) (n : Node) : Core P × Option Nat :=
  match h : c.1.addNode P n with
  | (r, t) => (⟨r, by have := Raw.addNode_ok c.2 n; rw [h] at this; exact this⟩, t)

def emit (c : Core P) (st : Step) : Core P := ⟨c.1.emit P st, Raw.emit_ok c.2 st⟩

def link (c : Core P) (hi lo s : Nat) : Core P × Bool :=
  match h : c.1.link hi lo s with
  | (r, t) => (⟨r, by have := Raw.link_ok c.2 hi lo s; rw [h] at this; exact this⟩, t)

def mark (c : Core P) (d : Nat) : Core P := ⟨c.1.mark d, Raw.mark_ok c.2 d⟩

def restore (c : Core P) (d keep : Nat) : Core P × Bool :=
  match h : c.1.restore d keep with
  | (r, t) => (⟨r, by have := Raw.restore_ok c.2 d keep; rw [h] at this; exact this⟩, t)

def goal (c : Core P) (o : Nat) (lhs rhs : Term) (s : Nat) : Core P × Bool :=
  match h : c.1.goal P o lhs rhs s with
  | (r, t) => (⟨r, by have := Raw.goal_ok c.2 o lhs rhs s; rw [h] at this; exact this⟩, t)

/-! ## What a state means -/

/-- A node and the root of its class have one value in every model of the
program. -/
theorem find_eq (c : Core P) (M : Model) (hM : ∀ p, M.Models P p) :
    ∀ i, nval M c.nodes i = nval M c.nodes (find c.parent i) := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    rw [find]
    split
    · rename_i p hp
      split
      · rename_i hlt
        obtain ⟨s, cc, -, hs, ha, hb⟩ := c.2.links i p hp hlt
        have := (c.2.valid M s cc hs).1 (hM _)
        rw [ha, hb] at this
        exact this.trans (ih p hlt)
      · rfl
    · rfl

/-- **Classes.** Two nodes of one class have one value in every model of the
program. -/
theorem class_sound (c : Core P) {a b : Nat} (h : find c.parent a = find c.parent b)
    (M : Model) (hM : ∀ p, M.Models P p) : nval M c.nodes a = nval M c.nodes b := by
  rw [find_eq c M hM a, find_eq c M hM b, h]

/-- **Goals.** A recorded `check-eq` holds in every model of the commands
before it. -/
theorem goal_sound (c : Core P) {o : Nat} {l r : Term} (h : (o, l, r) ∈ c.goals)
    (M : Model) (hM : M.Models P o) : M.eval l = M.eval r :=
  c.2.goals _ h M hM

end Core

end SemperCheck

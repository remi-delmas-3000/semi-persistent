import SemperCheck.Parse
import SemperCheck.Core
import Std.Data.HashMap

/-!
# The replayer

Reads the engine's event stream in order (`proofs/checker/REPLAY.md`) and
checks each event against its own classes: a table of node definitions and a
union-find over node ids.

The table, the classes and the proved `check-eq` are a `Core P`
(`Core.lean`), which only its proved operations build: a node enters the table
if it is well-sorted, a kernel step's conclusion is recorded if the kernel's
check accepts the step, and two classes are joined only by a link that a
recorded conclusion proves. Each event's check is the construction of the
kernel steps that justify its merge, from the event's witnesses and the
current classes; a merge whose steps the kernel rejects is not applied.
`ReplaySound.lean` states what follows for the state after any stream.
-/

namespace SemperCheck.Replay

open SemperCheck

/-- What a node id stands for. -/
abbrev Def := Node

abbrev Spell := Std.HashMap (String × List Nat) Nat

structure St (P : Program) where
  declAt : Std.HashMap Nat Decl := {}
  /-- The node table, the kernel conclusions, the classes with the step that
  proves each link, the classes at each mark and at the round's start, and
  the `check-eq` proved. -/
  core : Core P := Core.new P
  /-- The table id of each of the engine's node ids. A restore discards the
  engine's ids past the mark, and the engine reuses them; the table keeps its
  nodes. -/
  cid : Array (Option Nat) := #[]
  /-- `(f, c1 .. ck) -> id`: the program term `f(c1 .. ck)` evaluated to `id`. -/
  spell : Spell := {}
  /-- The node of each operator's unit (`z` lines). -/
  units : Std.HashMap String Nat := {}
  /-- Each literal's node, checked against its definition on use. -/
  lits : Std.HashMap (String × String) Nat := {}
  /-- Each mark: the number of engine ids, the plain members and the spelling
  table at the mark. The classes at the mark are in `core`. -/
  snaps : Array (Nat × Array (Option Nat) × Spell) := #[]
  /-- For a class's root, a member that is no application of an associative
  operator, when the class has one. A monomial's term names a class by such a
  member: the kernel reads through an application of the operator, and would
  read the class's root as its arguments. -/
  plain : Array (Option Nat) := #[]
  /-- For a node, the last program term that evaluated to it: the term's
  table id and the proof that the term is the node. -/
  lastTerm : Std.HashMap Nat (Nat × Option (Option Nat)) := {}
  /-- For a program term's table id, the node it evaluated to and the proof. -/
  byTerm : Std.HashMap Nat (Nat × Option (Option Nat)) := {}
  /-- The kind of the line being replayed, and the merges whose kernel steps
  were not found or not accepted, by kind. None of them is applied. -/
  cur : String := ""
  nUnjustified : Nat := 0
  unjustified : Std.HashMap String Nat := {}
  /-- Splice witnesses for the next `t`, `c` or `w` line. -/
  splices : List (Nat × Nat) := []
  /-- Inverse witnesses (`j` lines) for the next line: inverse applications,
  each standing for its class. -/
  inverses : List Nat := []
  /-- The open firing: its command's offset, and whether it is a `rewrite`. -/
  fire : Option (Nat × Bool) := none
  atoms : Array (Nat × String × List Nat) := #[]
  /-- The right-hand side's nodes; `true` marks a `let` name's node. -/
  rhs : List (Nat × Bool) := []
  /-- The `check-eq` whose two nodes were in one class at their `g` line. -/
  proved : List Nat := []
  events : Nat := 0
  failed : Std.HashMap String Nat := {}
  nFailed : Nat := 0
  lastCause : String := ""
  unchecked : Std.HashMap String Nat := {}

variable {P : Program}

instance : Inhabited (St P) := ⟨{}⟩

/-- The program replayed against. -/
@[reducible] def St.prog (_S : St P) : Program := P

namespace St

def defs (S : St P) : Array Node := S.core.nodes

def index (S : St P) : Std.HashMap Node Nat := S.core.index

def fd (S : St P) (i : Nat) : Nat := find S.core.parent i

def defOf (S : St P) (i : Nat) : Option Def := S.core.nodes[i]?

/-- The table id of the engine's node `i`. -/
def tr (S : St P) (i : Nat) : Option Nat := S.cid.getD i none

def node? (S : St P) (x : String) : Option Nat := x.toNat?.bind S.tr

def fail (S : St P) (cause : String) : St P :=
  { S with failed := S.failed.insert cause (S.failed.getD cause 0 + 1), nFailed := S.nFailed + 1, lastCause := cause,
           splices := [], inverses := [] }

/-- Runs `k` on the checked state, taken out of `S` while `k` runs so that
its arrays are held once and updated in place. -/
@[inline] def withCore {α : Type} (S : St P) (k : Core P → Core P × α) : St P × α :=
  let c := S.core
  let S := { S with core := Core.new P }
  let (c, x) := k c
  ({ S with core := c }, x)

/-- The state with the classes of the round's start as its classes. -/
def atRound (S : St P) : St P := { S with core := S.core.atRound }

end St

/-! ## Proofs

A proof that two nodes are equal is `none` (the replayer has no kernel step),
`some none` (they are one node), or `some (some s)` (step `s` concludes it). -/

abbrev Pf := Option (Option Nat)

/-- Has the kernel check step `st`, and gives its index. The kernel records
the step's conclusion, or `0 = 0` for a step it rejects. -/
def emit (S : St P) (st : Step) (_a _b : Nat) : St P × Nat :=
  S.withCore fun c =>
    -- The size is read first: reading it after the push would keep a second
    -- reference to the array and make the push copy it.
    let n := c.acc.size
    (c.emit st, n)

/-- `x = y` from `x = y`'s reverse. -/
def symmP (S : St P) (x y : Nat) : Pf → St P × Pf
  | some (some s) => let (S, t) := emit S (.symm s) y x; (S, some (some t))
  | p => (S, p)

/-- `x = z` from `x = y` and `y = z`. -/
def transP (S : St P) (_x _z : Nat) : Pf → Pf → St P × Pf
  | some none, q => (S, q)
  | p, some none => (S, p)
  | some (some s), some (some t) =>
    -- The kernel needs the first step to end where the second starts.
    match S.core.acc[s]?, S.core.acc[t]? with
    | some c, some d =>
      if c.b == d.a then let (S, u) := emit S (.trans s t) c.a d.b; (S, some (some u)) else (S, none)
    | _, _ => (S, none)
  | _, _ => (S, none)

/-- A step that concludes `x = y`, a reflexivity when they are one node. -/
def stepOf (S : St P) (x : Nat) : Pf → St P × Option Nat
  | some (some s) => (S, some s)
  | some none => let (S, s) := emit S (.refl x) x x; (S, some s)
  | none => (S, none)

/-- Points `hi` at `lo`, if step `s` concludes `hi = lo`. -/
def St.link (S : St P) (hi lo s : Nat) : St P × Bool := S.withCore fun c => c.link hi lo s

/-- The root of `i`'s class and the proof that `i` is it. -/
def findP (S : St P) (i : Nat) : St P × Nat × Pf :=
  match S.core.parent[i]? with
  | some p =>
    if _h : p < i then
      let (S, r, q) := findP S p
      match S.core.proof.getD i none with
      | some s =>
        let (S, pf) := transP S i r (some (some s)) q
        -- Point `i` at its root, with the proof just composed.
        match pf with
        | some (some t) =>
          if r != p then ((S.link i r t).1, r, pf) else (S, r, pf)
        | _ => (S, r, pf)
      | none => (S, r, none)
    else (S, i, some none)
  | none => (S, i, some none)
termination_by i

/-- The proof that `x` and `y`, of one class, are equal. -/
def eqP (S : St P) (x y : Nat) : St P × Pf :=
  if x == y then (S, some none)
  else
    let (S, rx, px) := findP S x
    let (S, ry, py) := findP S y
    if rx != ry then (S, none)
    else
      let (S, qy) := symmP S y ry py
      transP S x y px qy

def St.noStep (S : St P) : St P :=
  { S with unjustified := S.unjustified.insert S.cur (S.unjustified.getD S.cur 0 + 1),
           nUnjustified := S.nUnjustified + 1 }

/-- Merges the classes of `a` and `b`, which `pf` proves equal: the link
between the two roots carries the step that proves them equal. Without such a
step, accepted by the kernel, the classes stay apart. -/
def St.mergeBy (S : St P) (a b : Nat) (pf : Pf) : St P :=
  let (S, ra, pa) := findP S a
  let (S, rb, pb) := findP S b
  if ra == rb then S
  else
    -- `hi = lo`, through `a = b` in the direction that starts at `hi`.
    let (S, link) :=
      if ra > rb then
        let (S, q) := symmP S a ra pa
        let (S, q) := transP S ra b q pf
        transP S ra rb q pb
      else
        let (S, q) := symmP S b rb pb
        let (S, r) := symmP S a b pf
        let (S, q) := transP S rb a q r
        transP S rb ra q pa
    let (lo, hi) := (min ra rb, max ra rb)
    match link with
    | some (some s) =>
      match S.link hi lo s with
      | (S, true) =>
        -- The merged class keeps a plain member of either side.
        match S.plain.getD lo none, S.plain.getD hi none with
        | none, some m =>
          let plain := if S.plain.size ≤ lo then S.plain ++ Array.replicate (lo + 1 - S.plain.size) none
            else S.plain
          { S with plain := plain.setIfInBounds lo (some m) }
        | _, _ => S
      | (S, false) => S.noStep
    | _ => S.noStep

/-- A merge the replayer has no kernel step for: it is not applied. -/
def St.merge (S : St P) (a b : Nat) : St P := S.mergeBy a b none

mutual

/-- The node a program term evaluated to, through the spelling table. -/
def eval (S : St P) : Term → Option Nat
  | .lit s v =>
    match S.lits[(s, v)]? with
    | some n =>
      match S.defOf n with
      | some (.lit s' v') => if s' == s && v' == v then some n else none
      | _ => none
    | none => none
  | .app f args =>
    (evalArgs S (if S.prog.kind f == .assoc then some f else none) args).bind fun ids =>
      S.spell[(f, ids)]?

/-- The nodes of a term's arguments. With `fl = some f`, the arguments of a
nested application of `f` take its place, as the engine's term builder
splices them before the arguments are built. -/
def evalArgs (S : St P) (fl : Option String) : List Term → Option (List Nat)
  | [] => some []
  | .app g xs :: rest =>
    if fl == some g && !xs.isEmpty then
      (evalArgs S fl xs).bind fun a => (evalArgs S fl rest).map (a ++ ·)
    else (eval S (.app g xs)).bind fun a => (evalArgs S fl rest).map (a :: ·)
  | .lit s v :: rest => (eval S (.lit s v)).bind fun a => (evalArgs S fl rest).map (a :: ·)

end

mutual

/-- Node `n`'s definition is the term `t`, argument for argument. -/
def denotes (S : St P) (n : Nat) : Term → Bool
  | .lit s v => match S.defOf n with
    | some (.lit s' v') => s' == s && v' == v
    | _ => false
  | .app f ts => match S.defOf n with
    | some (.app g cs) => g == f && denotesArgs S cs ts
    | _ => false

def denotesArgs (S : St P) : List Nat → List Term → Bool
  | [], [] => true
  | c :: cs, t :: ts => denotes S c t && denotesArgs S cs ts
  | _, _ => false

end

/-- The node of `f`'s unit: the one a `z` line named, if its definition still
is the declared unit (a restore can have discarded it). -/
def St.unit (S : St P) (f : String) : Option Nat :=
  match S.units[f]?, (S.prog.opDecl? f).bind (·.unit) with
  | some u, some t => if denotes S u t then some u else none
  | _, _ => none

/-- The applications of `f` among `xs` and, literally nested, below them:
each is a splice witness for its own class. -/
def nested (defs : Array Node) (f : String) (x : Nat) : List (Nat × List Nat) :=
  match defs[x]? with
  | some (.app g cs) =>
    if g == f && !cs.isEmpty then
      (x, cs) :: cs.flatMap fun c => if _h : c < x then nested defs f c else []
    else []
  | _ => []
termination_by x

/-- `a`, or the arguments a witness for `a`'s class splices in. A class is
not expanded inside its own expansion: each expansion removes its witness. -/
def expand (S : St P) (W : List (Nat × List Nat)) (a : Nat) : List Nat :=
  match h : W.find? (·.1 == S.fd a) with
  | some (_, cs) => cs.flatMap (expand S (W.filter (·.1 != S.fd a)))
  | none => [a]
termination_by W.length
decreasing_by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  rw [List.length_unattach]
  conv => rhs; rw [← List.length_attach (l := W)]
  apply List.length_filter_lt_length_iff_exists.2
  exact ⟨⟨_, hm⟩, List.mem_attach _ _, by simp_all⟩

/-- Removes each argument that is `inv` applied to a node together with one
argument in that node's class; with `unit` given, also each argument that is
`inv` applied to a node of the unit's class. -/
def cancelInverse (S : St P) (inv : String) (unit : Option Nat) (xs : List Nat) : List Nat := Id.run do
  -- What `a` is the inverse of: its own argument, or that of a witness (`j`
  -- line) in its class.
  let inverseOf (a : Nat) : Option Nat :=
    let arg (m : Nat) : Option Nat :=
      match S.defOf m with
      | some (.app g [y]) => if g == inv then some y else none
      | _ => none
    (arg a).orElse fun _ => S.inverses.findSome? fun m => if S.fd m == S.fd a then arg m else none
  let mut out := xs.toArray
  for a in xs do
    if let some y := inverseOf a then
      if let some i := out.findIdx? (· == a) then
        let rest := out.eraseIdxIfInBounds i
        -- `inv(e)` is `e`: with `unit` given, it goes by itself.
        if unit == some (S.fd y) then out := rest
        else if let some j := rest.findIdx? (fun b => S.fd b == S.fd y) then
          out := rest.eraseIdxIfInBounds j
  return out.toList

/-- Sorted classes with each class's count reduced modulo `n`. -/
def modCount (n : Nat) (xs : List Nat) : List Nat :=
  let groups := xs.foldl (fun (acc : List (Nat × Nat)) c =>
    match acc with
    | (d, k) :: rest => if d == c then (d, k + 1) :: rest else (c, 1) :: acc
    | [] => [(c, 1)]) []
  groups.reverse.flatMap fun (c, k) => List.replicate (k % n) c

/-- The normal forms, as classes, of the argument lists `as` and `bs` of `f`.
An associative operator's argument is one class unless a witness splices it:
the engine's (`s` lines, checked here), or an application of `f` that appears
among the arguments, which witnesses its own class. Both lists use the same
witnesses. -/
def nf2 (S : St P) (f : String) (as bs : List Nat) (invUnit : Bool := false) : List Nat × List Nat :=
  match S.prog.kind f with
  | .plain => (as.map S.fd, bs.map S.fd)
  | .comm => ((as.map S.fd).mergeSort (· ≤ ·), (bs.map S.fd).mergeSort (· ≤ ·))
  | k =>
    let given := S.splices.filterMap fun (c, m) =>
      match S.defOf m with
      | some (.app g cs) => if g == f && !cs.isEmpty && S.fd m == S.fd c then some (S.fd c, cs) else none
      | _ => none
    let own := ((as ++ bs).flatMap (nested S.defs f)).map fun (x, cs) => (S.fd x, cs)
    let W := given ++ own
    let u := (S.unit f).map S.fd
    let d := S.prog.opDecl? f
    let one (xs : List Nat) : List Nat :=
      -- The unit's arguments go first, as in the engine: `f(e, inv(e))` is
      -- `inv(e)`, which is in `e`'s class only once that is derived.
      let atoms := (xs.flatMap (expand S W)).filter fun a => some (S.fd a) != u
      let atoms := match k, d.bind (·.inverse) with
        | .assoc, _ => atoms
        | _, some inv => cancelInverse S inv (if invUnit then u else none) atoms
        | _, none => atoms
      let cls := atoms.map S.fd
      match k with
      | .assoc => cls
      | .ac =>
        let cls := cls.mergeSort (· ≤ ·)
        match d.bind (·.nilpotent) with
        | some n => if n > 0 then modCount n cls else cls
        | none => cls
      | _ => (cls.mergeSort (· ≤ ·)).eraseDups
    (one as, one bs)

/-- Node `n` has the value of `f(cs)`: it is an application of `f` whose
arguments have the same normal form, or the normal form is the one class of
`n`, or it is empty and `n` is in the unit's class. -/
def spells (S : St P) (n : Nat) (f : String) (cs : List Nat) : Bool :=
  -- An inverse of a node of the unit's class goes by itself: `inv(e) = e`.
  let invUnit := true
  (match S.defOf n with
      | some (.app g ds) => g == f && (let (x, y) := nf2 S f ds cs invUnit; x == y)
      | _ => false)
    || ((S.prog.kind f).isAssoc &&
        (let t := (nf2 S f cs [] invUnit).1
         -- One class left: the application is that class. None left: it is the unit.
         t == [S.fd n] || (t.isEmpty && (S.unit f).map S.fd == some (S.fd n))))

/-! ## Completion merges

Both merged nodes derive from one start monomial: each side rewrites it by
rules, in order, where a rule is a pair of nodes in one class and a rewrite
replaces the left node's arguments by the right node's. The replayer keeps a
monomial as a list of argument nodes, so that an inverse application stays
recognizable, and reduces it by the operator's laws after each rewrite. -/

/-- A monomial reduced by `f`'s laws: inverse pairs and the unit's class
removed, and each class kept once (ACI) or its count modulo `n`
(`:nilpotent n`). -/
def lawReduce (S : St P) (f : String) (atoms : List Nat) (inverse : Bool := true)
    (peak : Bool := false) : List Nat :=
  let d := S.prog.opDecl? f
  let u := (S.unit f).map S.fd
  let dropUnit (xs : List Nat) : List Nat := xs.filter fun a => some (S.fd a) != u
  -- The unit's arguments go before the inverse pairs are cancelled, except in
  -- the peak of a critical pair with the inverse law (`peak`), which is a
  -- rule's left side and the inverse of one of its arguments: that pair is
  -- cancelled even when one of the two is in the unit's class.
  let live : List Nat := match inverse, d.bind (fun d => d.inverse) with
    | true, some inv =>
      if peak then dropUnit (cancelInverse S inv none atoms)
      else cancelInverse S inv u (dropUnit atoms)
    | _, _ => dropUnit atoms
  -- Each class with its atoms, in order of first occurrence.
  let groups : Array (Nat × Array Nat) := live.foldl (fun groups a =>
    let c := S.fd a
    match groups.findIdx? (fun g => g.1 == c) with
    | some i => groups.modify i fun (c, xs) => (c, xs.push a)
    | none => groups.push (c, #[a])) #[]
  let keep (limit : Nat → Nat) : List Nat :=
    groups.toList.flatMap fun (_, xs) => (xs.toList.take (limit xs.size))
  match S.prog.kind f, d.bind (fun d => d.nilpotent) with
  | .aci, _ => keep fun _ => 1
  | _, some n => if n > 0 then keep (fun k => k % n) else live
  | _, none => live

/-- The classes of a monomial, sorted. -/
def classesOf (S : St P) (atoms : List Nat) : List Nat := (atoms.map S.fd).mergeSort (· ≤ ·)

def countOf (c : Nat) (xs : List Nat) : Nat := (xs.filter (· == c)).length

/-- Removes `k` atoms of class `c`. -/
def dropClass (S : St P) (c : Nat) : Nat → List Nat → List Nat
  | 0, xs => xs
  | _, [] => []
  | k + 1, x :: xs => if S.fd x == c then dropClass S c k xs else x :: dropClass S c (k + 1) xs

/-- The monomial `m` with the classes `l` replaced by the atoms `r`, as many
times as `m` holds `l` (once under ACI or a nilpotent law, where a class's
count is bounded, and once when `once` is set). `none` when `m` does not hold `l`. -/
def applyRule (S : St P) (f : String) (m : List Nat) (l : List Nat) (r : List Nat) (once : Bool := false) :
    Option (Nat × List Nat × List Nat) :=
  let mc := classesOf S m
  let distinct := l.eraseDups
  if l.isEmpty || !distinct.all (fun c => countOf c mc ≥ countOf c l) then none
  else
    let bounded := S.prog.kind f == .aci || ((S.prog.opDecl? f).bind (·.nilpotent)).isSome
    let q := if bounded || once then 1
      else distinct.foldl (fun q c => min q (countOf c mc / countOf c l)) (mc.length + 1)
    let rest := distinct.foldl (fun m c => dropClass S c (q * countOf c l) m) m
    -- Between rewrites the engine clamps counts and drops the unit; it cancels
    -- inverse pairs on the normal form only.
    some (q, rest, lawReduce S f (rest ++ (List.replicate q r).flatten) (inverse := false))

/-- The arguments of `x` as a monomial of `f`: its own, if it is an
application of `f`, else `x` itself. -/
def monomial (S : St P) (f : String) (W : List (Nat × List Nat)) (x : Nat) : List Nat :=
  -- A node that is one argument is still expanded when a witness splices its
  -- class: every list of one event reads a class the same way.
  match S.defOf x with
  | some (.app g cs) => if g == f && !cs.isEmpty then cs.flatMap (expand S W) else expand S W x
  | _ => expand S W x

/-- One rewrite of a monomial, for the kernel steps that follow it: the rule's
two nodes, the number of copies rewritten, the arguments left untouched, and
the monomial after. -/
structure Rewrote where
  l : Nat
  r : Nat
  q : Nat
  rest : List Nat
  after : List Nat
  /-- The right side is `r` as one argument. -/
  atom : Bool := false

/-- Rewrites `m` by the rules `rules`, in order: the result and each rewrite.
Monomials are read on the classes of `S`; a rule's two nodes are in one class
of `now`, the current classes. -/
def rewrite (now S : St P) (f : String) (W : List (Nat × List Nat)) (m : List Nat) (once : Bool := false)
    (done : Array Rewrote := #[]) : List (Nat × Nat × Bool) → Except String (List Nat × Array Rewrote)
  | [] => pure (m, done)
  | (l, r, atom) :: rest => do
    if now.fd l != now.fd r then throw "completion: rule sides in two classes"
    match S.defOf l with
    | some (.app g ls) =>
      if g != f then throw "completion: rule of another operator"
      let lc := classesOf S (lawReduce S f (ls.flatMap (expand S W)))
      match applyRule S f m lc (if atom then [r] else monomial S f W r) once with
      | some (q, left, m') => rewrite now S f W m' once (done.push { l, r, q, rest := left, after := m', atom }) rest
      | none => throw "completion: rule does not apply"
    | _ => throw "completion: rule of another operator"

/-- The monomial `m` has the value of node `t`: it is `t`'s arguments, or it
is the one class of `t` (a result of one argument is that argument's class,
whose root can itself be an application of `f`). -/
def reaches (S : St P) (f : String) (W : List (Nat × List Nat)) (m : List Nat) (t : Nat) : Bool :=
  let c := classesOf S (lawReduce S f m)
  c == classesOf S (lawReduce S f (monomial S f W t)) || c == [S.fd t]

/-- The splice witnesses a completion event shares: the applications of `f`
nested in the arguments of the nodes it names. -/
def lawWitnesses (S : St P) (f : String) (nodes : List Nat) : List (Nat × List Nat) :=
  (nodes.flatMap fun x =>
    match S.defOf x with
    | some (.app g cs) => if g == f then cs.flatMap (nested S.defs f) else []
    | _ => []).map fun (x, cs) => (S.fd x, cs)

/-- Rules as the stream writes them: `l r k`, with `k = 1` when the right
side is `r` as one argument and `0` when it is `r`'s own arguments. -/
def pairs : List Nat → List (Nat × Nat × Bool)
  | l :: r :: k :: rest => (l, r, k == 1) :: pairs rest
  | _ => []

/-- The rules of a line, their nodes as table ids. -/
def rules (S : St P) (xs : List Nat) : Option (List (Nat × Nat × Bool)) :=
  (pairs xs).mapM fun (l, r, k) => do pure (← S.tr l, ← S.tr r, k)

/-- A derivation the kernel steps follow: from a node, or from the term of a
monomial, through the monomial it reduces to and each rewrite, to a node. -/
structure Chain where
  f : String
  start : Nat ⊕ List Nat
  /-- The start is the peak of a critical pair with a law, and `first` is the
  peak reduced by that law. -/
  peak : Bool := false
  first : List Nat
  steps : Array Rewrote
  target : Nat ⊕ List Nat

/-- The derivations of a critical pair: each side from the peak; with a
cancellation, each side first to its monomial before it, then `left`, `right`
(what stays of each side) and `common` (what both lose), then each side from
what stays. -/
structure PeakPlan where
  a : Chain
  b : Chain
  cancel : Option (List Nat × List Nat × List Nat × Chain × Chain) := none

/-- `i a b n l1 r1 ..`: node `n`, a member of one merged class, rewrites by
the rules to the other merged node. The engine computes a round's rewrites on
the classes at the round's start (`R`), and builds the nodes it merges on the
current ones (`S`): the derivation is read on `R`, its ends on `S`. -/
def interReduce (S R : St P) (a b n : Nat) (rules : List (Nat × Nat × Bool)) : Except String Chain := do
  let some (.app f as) := S.defOf n | throw "completion: start is not an application"
  unless (S.prog.kind f).isAssoc && S.prog.kind f != .assoc do throw "completion: not an AC operator"
  let t ← if S.fd n == S.fd b then pure a else if S.fd n == S.fd a then pure b
    else throw "completion: start in neither class"
  -- A monomial is a node's arguments, each one class, as the engine reads it.
  let W : List (Nat × List Nat) := []
  let first := lawReduce R f (as.flatMap (expand R W))
  let (m, steps) ← rewrite S R f W first false #[] rules
  unless reaches S f W m t do throw "completion: normal form differs"
  pure { f, start := .inl n, first, steps, target := .inl t }

/-- The witnesses of a critical-pair merge (`p` line). -/
structure Peak where
  cancel : Bool
  reduceB : Bool
  keep : Option Nat
  peak : List Nat
  preA : List (Nat × Nat × Bool)
  preB : List (Nat × Nat × Bool)
  postA : List (Nat × Nat × Bool)
  postB : List (Nat × Nat × Bool)

/-- Reads the fields after `p a b`: `cancel reduceB hasKeep [keep] k peak..
na (l r).. nb (l r).. npa (l r).. (l r)..`. -/
def Peak.read (S : St P) (xs : List Nat) : Option Peak := do
  let (cancel, xs) ← xs.head?.map (·, xs.tail)
  let (reduceB, xs) ← xs.head?.map (·, xs.tail)
  let (hasKeep, xs) ← xs.head?.map (·, xs.tail)
  let (keep, xs) ← if hasKeep == 1 then xs.head?.bind (fun k => (S.tr k).map fun k => (some k, xs.tail))
    else some (none, xs)
  let (k, xs) ← xs.head?.map (·, xs.tail)
  if xs.length < k then none
  let (peak, xs) := (← (xs.take k).mapM S.tr, xs.drop k)
  let (na, xs) ← xs.head?.map (·, xs.tail)
  if xs.length < 3 * na then none
  let (preA, xs) := (← rules S (xs.take (3 * na)), xs.drop (3 * na))
  let (nb, xs) ← xs.head?.map (·, xs.tail)
  if xs.length < 3 * nb then none
  let (preB, xs) := (← rules S (xs.take (3 * nb)), xs.drop (3 * nb))
  let (npa, xs) ← xs.head?.map (·, xs.tail)
  if xs.length < 3 * npa then none
  return { cancel := cancel == 1, reduceB := reduceB == 1, keep, peak, preA, preB,
           postA := ← rules S (xs.take (3 * npa)), postB := ← rules S (xs.drop (3 * npa)) }

/-- `p a b ..`: the merged nodes `a` and `b` are what the two sides of a
critical pair rewrite to. Both sides start from the peak (side B from the
peak reduced by the laws, with `reduceB`) and rewrite it by their rules; with
`cancel`, the common part of the two results is then removed (except one
occurrence of `keep`'s class), which the operator's `:cancellative` law
allows when both sides stay non-empty or the operator has a unit; each side
then rewrites by its remaining rules. -/
def peakMerge (S R : St P) (a b : Nat) (w : Peak) :
    Except String PeakPlan := do
  let named := a :: b :: (w.preA ++ w.preB ++ w.postA ++ w.postB).flatMap fun (l, r, _) => [l, r]
  -- The operator: that of the first rule, else of a merged node.
  let some f := (named.reverse.findSome? fun x =>
      match S.defOf x with
      | some (.app g _) => if (S.prog.kind g).isAssoc && S.prog.kind g != .assoc then some g else none
      | _ => none)
    | throw "completion: no AC operator"
  -- A monomial is a node's arguments, each one class, as the engine reads it.
  let W : List (Nat × List Nat) := []
  let peak := w.peak.flatMap (expand R W)
  -- A critical pair's own rules rewrite the peak once each; the normal form's
  -- rules, after it, rewrite every copy.
  let firstB := if w.reduceB then lawReduce R f peak (peak := true) else peak
  let (mA, sA) ← rewrite S R f W peak true #[] w.preA
  let (mB, sB) ← rewrite S R f W firstB true #[] w.preB
  if w.cancel then
    -- Declared, or a consequence of the group laws (`:inverse`).
    unless ((S.prog.opDecl? f).map fun d => d.cancellative || d.inverse.isSome).getD false do
      throw "completion: operator is not cancellative"
    let (mA, mB) := (lawReduce R f mA, lawReduce R f mB)
    let (ca, cb) := (classesOf R mA, classesOf R mB)
    let keep := w.keep.map R.fd
    -- The common part: each class, as many times as both sides hold it.
    let common := ca.eraseDups.map fun c =>
      (c, min (countOf c ca) (countOf c cb) - (if some c == keep then 1 else 0))
    let drop (m : List Nat) := common.foldl (fun m (c, k) => dropClass R c k m) m
    let (left, right) := (drop mA, drop mB)
    unless (!left.isEmpty && !right.isEmpty) || (S.unit f).isSome do
      throw "completion: cancellation empties a side"
    let (mA', tA) ← rewrite S R f W left false #[] w.postA
    let (mB', tB) ← rewrite S R f W right false #[] w.postB
    unless reaches S f W mA' a && reaches S f W mB' b do throw "completion: normal form differs"
    -- What side A loses: its arguments that are not in `left`.
    let gone := left.foldl (fun m x => m.erase x) mA
    pure { a := { f, start := .inr peak, first := peak, steps := sA, target := .inr mA },
           b := { f, start := .inr peak, peak := w.reduceB, first := firstB, steps := sB, target := .inr mB },
           cancel := some (left, right, gone,
             { f, start := .inr left, first := left, steps := tA, target := .inl a },
             { f, start := .inr right, first := right, steps := tB, target := .inl b }) }
  else
    let (mA, sA) ← rewrite S R f W mA false sA w.postA
    let (mB, sB) ← rewrite S R f W mB false sB w.postB
    unless reaches S f W mA a && reaches S f W mB b do throw "completion: normal form differs"
    pure { a := { f, start := .inr peak, first := peak, steps := sA, target := .inl a },
           b := { f, start := .inr peak, peak := w.reduceB, first := firstB, steps := sB, target := .inl b } }

/-- `v a b n1 n2`: a consequence of the group law of an operator `f` with
`:inverse g`, where `n1 = g(x1)` and `n2 = g(x2)` (`n2` is `n1` when one node
is enough). One of:
- `g` is injective: `n1` and `n2` in one class give `x1 = x2`;
- `g(g(z)) = z`: `x1` in the class of `n2` gives `n1 = x2`;
- `g(x) = e` exactly when `x = e`;
- under `:nilpotent k`: `f(x1, .., x1) = n1` and `f(n1, .., n1) = x1`, with
  `k - 1` arguments. -/
def groupLaw (S : St P) (a b n1 n2 : Nat) : Except String Unit := do
  let some (.app g [x1]) := S.defOf n1 | throw "group law: not an inverse node"
  let some (.app g' [x2]) := S.defOf n2 | throw "group law: not an inverse node"
  let some d := S.prog.ops.find? (fun d => d.inverse == some g && (d.kind == .ac || d.kind == .aci))
    | throw "group law: no operator with this inverse"
  unless g' == g do throw "group law: not an inverse node"
  let f := d.name
  let fd := S.fd
  let is (p q : Nat) : Bool := (fd a == fd p && fd b == fd q) || (fd a == fd q && fd b == fd p)
  let unit := (S.unit f).map fd
  -- `x` is what `k - 1` arguments in `y`'s class normalize to; `n1` stands
  -- for one of them when it is in that class, so that a self-inverse cancels.
  let power (x y : Nat) : Bool :=
    match d.nilpotent with
    | some (k + 1) =>
      let plain := List.replicate k y
      let withInv := if fd n1 == fd y && k > 0 then n1 :: List.replicate (k - 1) y else plain
      reaches S f [] plain x || reaches S f [] withInv x
    | _ => false
  let injective := fd n1 == fd n2 && is x1 x2
  let involution := fd x1 == fd n2 && is n1 x2
  let unitIn := (unit == some (fd n1) || unit == some (fd x1)) && is n1 x1
  let powers := (power a x1 && fd b == fd n1) || (power b x1 && fd a == fd n1) ||
    (power a n1 && fd b == fd x1) || (power b n1 && fd a == fd x1) ||
    -- `k - 1 = 1`: the power is its one argument.
    (d.nilpotent == some 2 && is n1 x1)
  unless injective || involution || unitIn || powers do throw "group law: no case applies"

/-- `c` and `c:k` fields as node ids, a counted one repeated. -/
def ids (S : St P) (xs : List String) : Option (List Nat) := do
  let mut out : Array Nat := #[]
  for x in xs do
    match x.splitOn ":" with
    | [n] => out := out.push (← S.node? n)
    | [n, k] =>
      let n ← S.node? n
      let k ← k.toNat?
      if k > 65536 then none
      for _ in [0:k] do out := out.push n
    | _ => none
  return out.toList

/-! ## Kernel steps for the checks -/

/-- The arguments node `x` flattens to under `f`, as the kernel's `view`
reads them: through every application of `f` nested in them. -/
def kview (S : St P) (f : String) (x : Nat) : List Nat :=
  match S.defOf x with
  | some (.app g cs) =>
    if g == f && !cs.isEmpty then cs.flatMap fun c => if _h : c < x then kview S f c else [c]
    else [x]
  | _ => [x]
termination_by x

/-- A `cong` step that concludes `a = b` for two nodes whose arguments the
replayer found equal as classes under `f`'s laws: its premises prove each
differing pair of arguments equal (plain and commutative operators), or send
each flattened argument to one node of its class, the unit's node for the
unit's class and the splice witness for a spliced class (associative
operators). `none` when a premise has no proof or the kernel's reading of the
two sides would differ. -/
def congStep (S : St P) (f : String) (a b : Nat) : St P × Pf := Id.run do
  if a == b then return (S, some none)
  let mut S := S
  let kind := S.prog.kind f
  if !kind.isAssoc then
    let (some (.app g as), some (.app h bs)) := (S.defOf a, S.defOf b) | return (S, none)
    if g != f || h != f || as.length != bs.length then return (S, none)
    let straight := (as.zip bs).all fun (c, d) => S.fd c == S.fd d
    let bs' := if !straight && kind == .comm then bs.reverse else bs
    let mut prems : Array Nat := #[]
    for (c, d) in as.zip bs' do
      if c != d then
        let (S', p) := eqP S c d
        S := S'
        match p with
        | some (some s) => prems := prems.push s
        | _ => return (S, none)
    let (S', s) := emit S (.cong f a b prems.toList) a b
    return (S', some (some s))
  -- Two applications whose arguments are equal one by one: the kernel takes
  -- them argument by argument, with no flattening, which is what an argument
  -- that is itself an application of `f`, standing for its class, needs.
  if let (some (.app g as), some (.app h bs)) := (S.defOf a, S.defOf b) then
    if g == f && h == f && as.length == bs.length && (as.zip bs).all (fun (c, d) => S.fd c == S.fd d) then
      let mut prems : Array Nat := #[]
      let mut ok := true
      for (c, d) in as.zip bs do
        if c != d && ok then
          let (S', p) := eqP S c d
          S := S'
          match p with
          | some (some st) => prems := prems.push st
          | _ => ok := false
      if ok then
        let (S', st) := emit S (.cong f a b prems.toList) a b
        return (S', some (some st))
  -- An associative operator: each flattened argument goes to its class's node.
  let va := kview S f a
  let vb := kview S f b
  let u := S.unit f
  let mut target : Std.HashMap Nat Nat := {}
  if let some u := u then target := target.insert (S.fd u) u
  for (c, m) in S.splices do
    match S.defOf m with
    | some (.app g cs) =>
      if g == f && !cs.isEmpty && S.fd m == S.fd c && !target.contains (S.fd c) then
        target := target.insert (S.fd c) m
    | _ => pure ()
  -- An application of `f` nested in either node's arguments: the kernel reads
  -- through it, so every argument of its class goes to it and is read the
  -- same way.
  let argsOf (x : Nat) : List Nat := match S.defOf x with
    | some (.app g cs) => if g == f then cs else []
    | _ => []
  for (m, _) in (argsOf a ++ argsOf b).flatMap (nested S.defs f) do
    if !target.contains (S.fd m) then target := target.insert (S.fd m) m
  for y in va ++ vb do
    if !target.contains (S.fd y) then target := target.insert (S.fd y) y
  -- The kernel's two sides: each argument's node, flattened, without the unit.
  let sideOf (v : List Nat) : List Nat :=
    (v.flatMap fun y => kview S f (target.getD (S.fd y) y)).filter fun y => some y != u
  let (la, lb) := (sideOf va, sideOf vb)
  let same := match kind with
    | .assoc => la == lb
    | .ac => la.mergeSort (· ≤ ·) == lb.mergeSort (· ≤ ·)
    | _ => la.all (lb.contains ·) && lb.all (la.contains ·)
  if !same then return (S, none)
  let mut prems : Array Nat := #[]
  let mut seen : Std.HashSet Nat := {}
  for y in va ++ vb do
    let t := target.getD (S.fd y) y
    if y != t && !seen.contains y then
      seen := seen.insert y
      let (S', p) := eqP S y t
      S := S'
      match p with
      | some (some s) => prems := prems.push s
      | _ => return (S, none)
  let (S', s) := emit S (.cong f a b prems.toList) a b
  return (S', some (some s))

/-- What `a` is the inverse of under `inv`, and the inverse application that
says so: `a` itself, or a witness (`j` line) in its class. -/
def inverseNode (S : St P) (inv : String) (a : Nat) : Option (Nat × Nat) :=
  let arg (m : Nat) : Option (Nat × Nat) :=
    match S.defOf m with
    | some (.app g [y]) => if g == inv then some (m, y) else none
    | _ => none
  (arg a).orElse fun _ => S.inverses.findSome? fun m => if S.fd m == S.fd a then arg m else none

/-- `f` applied to `m`, a node the kernel accepts, or `none`. -/
def appNode (S : St P) (f : String) (m : List Nat) : St P × Option Nat :=
  let d := Node.app f m
  if m.isEmpty then (S, none)
  else match S.index[d]? with
    | some t => (S, some t)
    | none =>
      -- The table takes the node only if it is well-sorted.
      S.withCore fun c => c.addNode d

/-- Node `x` reduced by `f`'s inverse and nilpotent laws, and the proof that
`x` is the result. Each inverse pair `y, g(y)` becomes `f(f(y, g(y)), rest)`
by `f`'s laws, then `f(e, rest)` by the `inv` step, then `f(rest)`; each `n`
arguments of one class under `:nilpotent n` likewise, by the `nil` step. An
inverse of a node of the unit's class is first proved to be the unit. -/
def lawNormP (S : St P) (f : String) (x : Nat) (peak : Bool := false) :
    St P × Option (Nat × Pf) := Id.run do
  let some d := S.prog.opDecl? f | return (S, some (x, some none))
  let some u := S.unit f | return (S, some (x, some none))
  if d.inverse.isNone && d.nilpotent.isNone then return (S, some (x, some none))
  let mut S := S
  let mut cur := x
  let mut pf : Pf := some none
  -- A bound on the passes: each removes at least one argument.
  -- In a critical pair's peak, an inverse pair is cancelled even when one of
  -- the two is in the unit's class: the unit's arguments stay.
  let mut atoms := (kview S f cur).filter fun a => peak || S.fd a != S.fd u
  for _ in [0:atoms.length + 1] do
    atoms := (kview S f cur).filter fun a => peak || S.fd a != S.fd u
    -- What the next pass replaces by the unit: a node `f(..)` that a step
    -- proves is the unit, and the arguments it stands for.
    let mut found : Option (Nat × Nat × List Nat) := none
    if let some g := d.inverse then
      for a in atoms do
        if found.isNone then
          if let some (q, y) := inverseNode S g a then
            if S.fd y == S.fd u then
              -- `f(y, g(y))` is the unit and, `y` being the unit, is `g(y)`.
              let (S1, pn) := appNode S f [y, q]
              S := S1
              if let some pn := pn then
                let (S1, s1) := emit S (.inv f pn y q u) pn u
                let (S1, p2) := congStep S1 f pn q
                let (S1, p3) := symmP S1 pn q p2
                let (S1, p4) := transP S1 q u p3 (some (some s1))
                S := S1.mergeBy q u p4
            else if let some b := (atoms.erase a).find? (fun b => S.fd b == S.fd y) then
              let (S1, pn) := appNode S f [y, q]
              S := S1
              if let some pn := pn then
                let (S1, s1) := emit S (.inv f pn y q u) pn u
                S := S1
                found := some (pn, s1, (atoms.erase a).erase b)
    if found.isNone then
      if let some (n + 1) := d.nilpotent then
        for a in atoms do
          if found.isNone then
            let same := atoms.filter fun b => S.fd b == S.fd a
            if same.length ≥ n + 1 then
              let (S1, pn) := appNode S f (a :: List.replicate n a)
              S := S1
              if let some pn := pn then
                let (S1, s1) := emit S (.nil f pn a n u) pn u
                S := S1
                let gone := same.take (n + 1)
                found := some (pn, s1, gone.foldl (fun m b => m.erase b) atoms)
    match found with
    | none => return (S, some (cur, pf))
    | some (pn, s1, rest) =>
      let (S1, t1) := appNode S f (pn :: rest)
      let (S1, t2) := appNode S1 f (u :: rest)
      S := S1
      let (some t1, some t2) := (t1, t2) | return (S, none)
      let (S1, t3) := if rest.isEmpty then (S, some u) else appNode S f rest
      S := S1
      let some t3 := t3 | return (S, none)
      let (S1, p1) := congStep S f cur t1
      let (S1, s2) := emit S1 (.cong f t1 t2 [s1]) t1 t2
      let (S1, p3) := congStep S1 f t2 t3
      let (S1, q) := transP S1 cur t2 p1 (some (some s2))
      let (S1, q) := transP S1 cur t3 q p3
      let (S1, q') := transP S1 x t3 pf q
      S := (S1.mergeBy cur t3 q)
      pf := q'
      cur := t3
      if q'.isNone then return (S, none)
  return (S, some (cur, pf))

/-- A step for `a = b` under `f`'s associativity, commutativity, idempotence
and unit, by the first of these that applies: `congStep`; all of one node's
arguments in the other's class; one node's arguments each standing for a
class, named by a plain member. -/
def congStepC (S : St P) (f : String) (a b : Nat) : St P × Pf :=
  let (S, p) := congStep S f a b
  if p.isSome then (S, p)
  else
  -- One node's arguments are all in the other's class (`f(x, x) = x` under
  -- ACI, or one argument): the node is one of them, which is the other node.
  let u := (S.unit f).map S.fd
  let collapse (S : St P) (x other : Nat) : St P × Pf :=
    let atoms := (kview S f x).filter fun y => some (S.fd y) != u
    match atoms.head? with
    | some y =>
      if x != y && atoms.all (fun z => S.fd z == S.fd other) then
        let (S, p1) := congStep S f x y
        let (S, p2) := eqP S y other
        transP S x other p1 p2
      else (S, none)
    | none => (S, none)
  let (S, p) := collapse S a b
  if p.isSome then (S, p)
  else
  let (S, p) := collapse S b a
  if p.isSome then (let (S, q) := symmP S b a p; (S, q))
  else
  -- `other`'s arguments stand for their classes, some of them applications of
  -- `f`: `x` is `f` of a plain member of each, by `f`'s laws, which is `other`
  -- argument by argument.
  let viaPlain (S : St P) (x other : Nat) : St P × Pf :=
    match S.defOf other with
    | some (.app g bs) =>
      if g != f || bs.isEmpty then (S, none)
      else
        let ps := bs.map fun y =>
          match S.defOf y with
          | some (.app h _) => if h == f then (S.plain.getD (S.fd y) none).getD y else y
          | _ => y
        if ps == bs then (S, none)
        else match appNode S f ps with
          | (S, some pn) =>
            let (S, p1) := congStep S f x pn
            if p1.isNone then (S, none)
            else
              let (S, p2) := congStep S f pn other
              transP S x other p1 p2
          | (S, none) => (S, none)
    | _ => (S, none)
  let (S, p) := viaPlain S a b
  if p.isSome then (S, p)
  else
  let (S, p) := viaPlain S b a
  if p.isSome then (let (S, q) := symmP S b a p; (S, q))
  else (S, none)

/-- `congStepC`, and when it gives no step for an operator with an inverse or
a nilpotent law: both nodes reduced by those laws, then `congStepC`. -/
def congStepL (S : St P) (f : String) (a b : Nat) (peak : Bool := false) : St P × Pf :=
  let (S, p) := congStepC S f a b
  if p.isSome then (S, p)
  else
    let laws := match S.prog.opDecl? f with
      | some d => d.inverse.isSome || d.nilpotent.isSome
      | none => false
    if !laws then (S, none)
    else
      match lawNormP S f a peak with
      | (S, some (ta, pa)) =>
        match lawNormP S f b with
        | (S, some (tb, pb)) =>
          let (S, p) := congStepC S f ta tb
          let (S, q) := transP S a tb pa p
          let (S, pb') := symmP S b tb pb
          transP S a b q pb'
        | (S, none) => (S, none)
      | (S, none) => (S, none)

/-- The kernel steps of a `v` line, whose check passed: the fact the line's
case rests on is derived from `inv` steps (`f(x, g(x))` is the unit), a `nil`
step for the powers, and a `cancel` step, and joins the classes; the proof of
the merge is then read from the classes. With `n1 = g(x1)`, `n2 = g(x2)`:
- `g(x1) = g(x2)` gives `f(x1, n1) = e = f(x2, n2) = f(x2, n1)`, so `x1 = x2`;
- `x1 = g(x2)` gives `f(n1, x1) = e = f(x2, n2) = f(x2, x1)`, so `n1 = x2`;
- `n1` or `x1` in the unit's class gives `f(x1, n1) = e` with one argument
  dropped, so the other is the unit;
- under `:nilpotent (k + 1)`, `f(x1^k, x1) = e = f(n1, x1)`, so `x1^k = n1`,
  and the same with `n1` and `x1` exchanged. -/
def groupLawP (S : St P) (a b n1 n2 : Nat) : St P × Pf := Id.run do
  let (some (.app g [x1]), some (.app _ [x2])) := (S.defOf n1, S.defOf n2) | return (S, none)
  let some d := S.prog.ops.find? (fun d => d.inverse == some g && (d.kind == .ac || d.kind == .aci))
    | return (S, none)
  let f := d.name
  let some u := S.unit f | return (S, none)
  let mut S := S
  -- `f(x, q) = e` for an inverse application `q = g(x)`: the node and the step.
  let invFact (S : St P) (x q : Nat) : St P × Option (Nat × Nat) :=
    match appNode S f [x, q] with
    | (S, some p) => let (S, s) := emit S (.inv f p x q u) p u; (S, some (p, s))
    | (S, none) => (S, none)
  let (S1, i1) := invFact S x1 n1
  let (S1, i2) := invFact S1 x2 n2
  S := S1
  let (some (p1, s1), some (p2, s2)) := (i1, i2) | return (S, none)
  -- `l = r` for two binary nodes proved equal to the unit by `sl`, `sr`.
  let viaUnit (S : St P) (l r : Nat) (sl sr : Pf) : St P × Pf :=
    let (S, q) := symmP S r u sr
    transP S l r sl q
  -- From `f(x, z) = f(y, z)`, proved by `pf` between nodes `l`, `r`: `x = y`.
  let cancel (S : St P) (l x y z : Nat) (pf : Pf) : St P :=
    match stepOf S l pf with
    | (S, some st) =>
      let (S, c) := emit S (.cancel f st x y z) x y
      S.mergeBy x y (some (some c))
    | (S, none) => S
  if S.fd n1 == S.fd u || S.fd x1 == S.fd u then
    -- One argument of `f(x1, n1)` is the unit: the node is the other one.
    let other := if S.fd x1 == S.fd u then n1 else x1
    let (S1, p) := congStep S f p1 other
    let (S1, q) := symmP S1 p1 other p
    let (S1, q) := transP S1 other u q (some (some s1))
    S := S1.mergeBy other u q
  if S.fd n1 == S.fd n2 && S.fd x1 != S.fd x2 then
    let (S1, qn) := appNode S f [x2, n1]
    S := S1
    if let some qn := qn then
      let (S1, e) := eqP S n1 n2
      let (S1, e) := stepOf S1 n1 e
      S := S1
      if let some e := e then
        let (S1, c) := emit S (.cong f qn p2 (if n1 == n2 then [] else [e])) qn p2
        let (S1, r) := transP S1 qn u (some (some c)) (some (some s2))
        let (S1, pf) := viaUnit S1 p1 qn (some (some s1)) r
        S := cancel S1 p1 x1 x2 n1 pf
  if S.fd x1 == S.fd n2 && S.fd n1 != S.fd x2 then
    let (S1, l) := appNode S f [n1, x1]
    let (S1, r) := appNode S1 f [x2, x1]
    S := S1
    if let (some l, some r) := (l, r) then
      let (S1, pl) := congStep S f l p1
      let (S1, pl) := transP S1 l u pl (some (some s1))
      let (S1, e) := eqP S1 x1 n2
      let (S1, e) := stepOf S1 x1 e
      S := S1
      if let some e := e then
        let (S1, c) := emit S (.cong f r p2 (if x1 == n2 then [] else [e])) r p2
        let (S1, pr) := transP S1 r u (some (some c)) (some (some s2))
        let (S1, pf) := viaUnit S1 l r pl pr
        S := cancel S1 l n1 x2 x1 pf
  if let some (k + 1) := d.nilpotent then
    if S.fd a != S.fd b then
      -- `y^k = w`, where `f(w, y) = e` is `f(x1, n1) = e` up to the order.
      for (y, w) in [(x1, n1), (n1, x1)] do
        if S.fd a != S.fd b then
          let (S1, t) := if k == 1 then (S, some y) else appNode S f (List.replicate k y)
          let (S1, n) := appNode S1 f (y :: List.replicate k y)
          S := S1
          if let (some t, some n) := (t, n) then
            let (S1, sn) := emit S (.nil f n y k u) n u
            let (S1, l) := appNode S1 f [t, y]
            let (S1, r) := appNode S1 f [w, y]
            S := S1
            if let (some l, some r) := (l, r) then
              let (S1, pl) := congStep S f l n
              let (S1, pl) := transP S1 l u pl (some (some sn))
              let (S1, pr) := congStep S1 f r p1
              let (S1, pr) := transP S1 r u pr (some (some s1))
              let (S1, pf) := viaUnit S1 l r pl pr
              S := cancel S1 l t w y pf
              -- The power's node is what the line merged with `w`.
              let other := if S.fd a == S.fd w then b else a
              if S.fd other != S.fd t then
                let (S1, p) := congStepL S f t other
                if p.isSome then S := S1.mergeBy t other p else S := S1
  return eqP S a b

mutual

/-- The table id of a program term as the kernel interns it: child for child. -/
def internT (S : St P) : Term → Option Nat
  | .lit s v => S.index[Node.lit s v]?
  | .app f args => (internTs S args).bind fun cs => S.index[Node.app f cs]?

def internTs (S : St P) : List Term → Option (List Nat)
  | [] => some []
  | t :: ts => (internT S t).bind fun a => (internTs S ts).map (a :: ·)

end

/-- The proof that the program term `t`, of table id `w`, is node `a`: the
one its `t` line recorded, when the term evaluated to `a`. -/
def termP (S : St P) (w a : Nat) : St P × Pf :=
  if w == a then (S, some none)
  else match S.byTerm[w]? with
    | some (n, p) =>
      let (S, q) := eqP S n a
      transP S w a p q
    | none => (S, none)

/-! ## One line -/

def sortOf (S : St P) (t : Nat) : Option String :=
  match S.defOf t with
  | some (.lit s _) => some s
  | some (.app f _) => (S.prog.opDecl? f).map (·.res)
  | none => none

/-- The table id of definition `d`, added to the table if it is new and
well-sorted. -/
def intern (S : St P) (d : Def) : St P × Option Nat :=
  match S.index[d]? with
  | some t => (S, some t)
  | none =>
    match S.withCore fun c => c.addNode d with
    | (S, some t) =>
      let isPlain := match d with
        | .lit _ _ => true
        | .app f _ => !(S.prog.kind f).isAssoc
      ({ S with plain := (if S.plain.size ≤ t then S.plain ++ Array.replicate (t + 1 - S.plain.size) none
                else S.plain).setIfInBounds t (if isPlain then some t else none) }, some t)
    | (S, none) => (S, none)

/-- A program term as the kernel interns it, the node it evaluated to, and
the proof that the two are equal: each argument's term is its node, and `f` of
the argument terms is the node by `f`'s laws (a nested application of an
associative operator, which the engine's term builder splices, among them).
The terms join their nodes' classes. -/
def writtenApp (S : St P) (f : String) (noArgs : Bool) (node : Option Nat) (ws : Array Nat) :
    St P × Option (Nat × Nat × Pf) := Id.run do
  let mut S := S
  let d := Node.app f ws.toList
  let w ← match S.index[d]? with
    | some w => pure w
    | none =>
      match intern S d with
      | (S', some w) =>
        S := S'
        pure w
      | (S', none) => return (S', none)
  match node with
  | some n =>
    -- `f()` is the unit, by the kernel's `unit` step.
    if noArgs && (S.prog.kind f).isAssoc then
      if let some u := S.unit f then
        let (S', st) := emit S (.unit f w u) w u
        let S' := S'.mergeBy w u (some (some st))
        let (S', p) := eqP S' w n
        return (S'.mergeBy w n p, some (w, n, p))
    let (S', p) := congStepL S f w n
    return (S'.mergeBy w n p, some (w, n, p))
  | none => return (S, some (w, w, some none))

mutual

def writtenP (S : St P) (t : Term) : St P × Option (Nat × Nat × Pf) :=
  match t with
  | .lit s v =>
    match S.index[Node.lit s v]? with
    | some n => (S, some (n, n, some none))
    | none => (S, none)
  | .app f args =>
    -- A nested application the engine's term builder spliced has no node of
    -- its own: the term then stands for itself.
    let node := eval S (.app f args)
    match writtenArgs S args #[] with
    | (S, some ws) => writtenApp S f args.isEmpty node ws
    | (S, none) => (S, none)

/-- Each argument's term, joined to the node it evaluated to. -/
def writtenArgs (S : St P) : List Term → Array Nat → St P × Option (Array Nat)
  | [], ws => (S, some ws)
  | a :: rest, ws =>
    match writtenP S a with
    | (S', some (w, m, p)) => writtenArgs (S'.mergeBy w m p) rest (ws.push w)
    | (S', none) => (S', none)

end

/-- The node of a monomial: `f` applied to its arguments, or the unit for
none. -/
def monoNode (S : St P) (f : String) (m : List Nat) (literal : Nat := 0) : St P × Option Nat :=
  if m.isEmpty then (S, S.unit f)
  else
    -- An argument that is an application of `f` stands for its class: name
    -- the class by a plain member, which the kernel reads as one argument.
    -- The first `literal` arguments are a rule's nodes, read as they are.
    let m := m.take literal ++ (m.drop literal).map fun x =>
      match S.defOf x with
      | some (.app g _) => if g == f then (S.plain.getD (S.fd x) none).getD x else x
      | _ => x
    let d := Node.app f m
    intern S d

/-- Node `x` with a plain member in place of each argument that is an
application of `f`: `x` itself when it has none, or is no application of `f`. -/
def plainArgs (S : St P) (f : String) (x : Nat) : St P × Option Nat :=
  match S.defOf x with
  | some (.app g cs) => if g == f && !cs.isEmpty then monoNode S f cs else (S, some x)
  | _ => (S, some x)

/-- The kernel steps of a derivation: the proof that its start is its
target, and the start's node. Each rewrite of `q` copies of `l` by `r` is
three `cong` steps: the monomial is `f(l, .., l, rest)` by `f`'s laws, which
is `f(r, .., r, rest)` argument by argument from `l = r`, which is the next
monomial by `f`'s laws. The nodes on the way join the start's class. -/
def emitChain (S : St P) (c : Chain) : St P × Option (Nat × Nat × Pf) := Id.run do
  let f := c.f
  let mut S := S
  let start ← match c.start with
    | .inl n => pure n
    | .inr m =>
      match monoNode S f m with
      | (S', some t) => S := S'; pure t
      | (S', none) => return (S', none)
  let mut cur := start
  let mut pf : Pf := some none
  -- One `cong` by `f`'s laws from the current node to `next`.
  let hop (S : St P) (cur next : Nat) (pf : Pf) (peak : Bool := false) : St P × Pf :=
    let (S, p) := congStepL S f cur next peak
    let S := S.mergeBy cur next p
    transP S start next pf p
  match monoNode S f c.first with
  | (S', some t) =>
    let (S', pf') := hop S' cur t pf c.peak
    S := S'; cur := t; pf := pf'
  | (S', none) => return (S', none)
  for st in c.steps do
    -- A right side that is one argument is named by a plain member of its
    -- class, which the kernel reads as one argument.
    let r := if st.atom then (S.plain.getD (S.fd st.r) none).getD st.r else st.r
    let (S1, t1) := monoNode S f (List.replicate st.q st.l ++ st.rest) st.q
    let (S2, t2) := monoNode S1 f (List.replicate st.q r ++ st.rest) st.q
    let (S3, t3) := monoNode S2 f st.after
    S := S3
    let (some t1, some t2, some t3) := (t1, t2, t3) | return (S, none)
    -- The kernel reads through the rule's node and through each of its
    -- arguments that is an application of `f`, which stands for its class.
    -- So the monomial is first `f(l', .., rest)`, where `l'` is `l` with a
    -- plain member for each such argument, and `l' = l` argument by argument.
    let (S', l') := plainArgs S f st.l
    S := S'
    if let some l' := l' then
      if l' != st.l then
        let (S', pl) := congStep S f l' st.l
        S := S'.mergeBy l' st.l pl
        let (S', t1') := monoNode S f (List.replicate st.q l' ++ st.rest) st.q
        S := S'
        let some t1' := t1' | return (S, none)
        let (S', pf') := hop S cur t1' pf
        S := S'; pf := pf'; cur := t1'
    let (S', pf') := hop S cur t1 pf
    S := S'; pf := pf'
    -- `f(l, .., rest) = f(r, .., rest)`: each differing argument is `l = r`.
    let (S', lr) := eqP S st.l r
    let (S', lrStep) := stepOf S' st.l lr
    S := S'
    let p2 : Pf ← if t1 == t2 then pure (some none) else
      match lrStep with
      | some e =>
        let (S', s2) := emit S (.cong f t1 t2 (if st.l == r then [] else [e])) t1 t2
        S := S'
        pure (some (some s2))
      | none => pure none
    S := S.mergeBy t1 t2 p2
    let (S', pf') := transP S start t2 pf p2
    S := S'; pf := pf'
    cur := t2
    -- The same for a right side read as its arguments.
    if !st.atom then
      let (S', r') := plainArgs S f r
      S := S'
      if let some r' := r' then
        if r' != r then
          let (S', pr) := congStep S f r r'
          S := S'.mergeBy r r' pr
          let (S', t2') := monoNode S f (List.replicate st.q r' ++ st.rest) st.q
          S := S'
          let some t2' := t2' | return (S, none)
          let (S', pf') := hop S cur t2' pf
          S := S'; pf := pf'; cur := t2'
    let (S', pf') := hop S cur t3 pf
    S := S'; cur := t3; pf := pf'
  let target ← match c.target with
    | .inl n => pure n
    | .inr m =>
      match monoNode S f m with
      | (S', some t) => S := S'; pure t
      | (S', none) => return (S', none)
  let (S', pf') := hop S cur target pf
  return (S', some (start, target, pf'))

/-- The kernel steps of a `t` line, whose check passed: the term as the
program writes it (its arguments' own terms as arguments) is node `i`. -/
def termLine (S : St P) (i : Nat) (f : String) (cs : List Nat) : St P := Id.run do
  let done (S : St P) : St P := { S with splices := [], inverses := [] }
  let ws := cs.map fun c => ((S.lastTerm[c]?).map (·.1)).getD c
  let (dW, dT) := (Node.app f ws, Node.app f cs)
  let (S, w) ← match intern S dW with
    | (S, some w) => pure (S, w)
    | (S, none) => return done S
  let (S, t2) ← match intern S dT with
    | (S, some t) => pure (S, t)
    | (S, none) => return done S
  let mut S := S
  -- The written term is `f` of the argument nodes: argument by argument.
  let mut p1 : Pf := some none
  if w != t2 then
    let mut prems : Array Nat := #[]
    let mut ok := true
    for (wc, c) in ws.zip cs do
      if wc != c then
        match (S.lastTerm[c]?).map (·.2) with
        | some (some (some s)) => prems := prems.push s
        | _ => ok := false
    if ok then
      let (S', s) := emit S (.cong f w t2 prems.toList) w t2
      S := S'
      p1 := some (some s)
    else p1 := none
  -- `f` of the argument nodes is the node, by the operator's laws.
  let (S', p2) := congStepL S f t2 i
  S := (S'.mergeBy t2 i p2).mergeBy w t2 p1
  let (S', p) := transP S w i p1 p2
  return { S' with lastTerm := S'.lastTerm.insert i (w, p), byTerm := S'.byTerm.insert w (i, p) }



/-! ## A rule firing

The walk matches the rule's patterns against the firing's lines, as before,
and builds what the kernel's `rule` step needs: the node of each pattern
instantiated by the assignment, and the proof that this instance is the node
the pattern matched or was built as. An instance joins that node's class. -/

structure Walk (P : Program) where
  S : St P
  σ : List (String × Nat) := []
  atoms : List (Nat × String × List Nat)
  rhs : List (Nat × Bool)
  /-- The matched node and the instance of each matched pattern, by the
  pattern's printed form. -/
  memo : List (String × Nat × Nat) := []

/-- The walk keeps its state when it fails: the replayer's state is in it,
and is held by one reference at a time so that its arrays are updated in
place. -/
abbrev WalkM (P : Program) := ExceptT String (StateM (Walk P))

def St.empty : St P := {}

/-- Runs `k` on the replayer's state, taken out of the walk while `k` runs. -/
def withS {α : Type} (k : St P → St P × α) : WalkM P α :=
  modifyGet fun w =>
    let S := w.S
    let w : Walk P := { w with S := {} }
    let (S, a) := k S
    (a, { w with S := S })

def key (p : Pat) : String := toString (repr p)

mutual

def Pat.toTerm? : Pat → Option Term
  | .var _ => none
  | .lit s v => some (.lit s v)
  | .app f ps => (Pat.toTerms? ps).map (.app f)

def Pat.toTerms? : List Pat → Option (List Term)
  | [] => some []
  | p :: ps => (Pat.toTerm? p).bind fun t => (Pat.toTerms? ps).map (t :: ·)

end

mutual

/-- The operator and the number of arguments of the first line a pattern's
match writes: that of its first innermost application or literal. -/
def firstLine : Pat → String × Nat
  | .var _ => ("", 0)
  | .lit _ _ => ("#lit", 0)
  | .app f ps => (firstOf ps).getD (f, ps.length)

/-- The first line of the first pattern that is no variable. -/
def firstOf : List Pat → Option (String × Nat)
  | [] => none
  | .var _ :: ps => firstOf ps
  | .lit s v :: _ => some (firstLine (.lit s v))
  | .app f qs :: _ => some (firstLine (.app f qs))

end

/-- The instance `f(ic)` of an application pattern, joined to node `n`. -/
def instOf (f : String) (ic : List Nat) (n : Nat) : WalkM P Nat := do
  let d := Node.app f ic
  let i ← withS fun S => intern S d
  match i with
  | some i =>
    withS fun S =>
      let (S, p) := congStepL S f i n
      (S.mergeBy i n p, i)
  | none => throw "rule: instance ill-sorted"

/-- A ground pattern that stands for a `let` name's term: its instance is
the term as the kernel interns it, joined to the name's node `n`. -/
def letInstance (p : Pat) (n : Nat) : WalkM P Nat := do
  match (Pat.toTerm? p).bind (internT (← get).S) with
  | some t =>
    withS fun S =>
      let (S, pf) := termP S t n
      (S.mergeBy t n pf, t)
  | none => pure n

/-- A ground argument the next line does not match is a `let` name's term:
the engine bound it to the name's node and wrote no line for it. -/
def groundNode (q : Pat) : WalkM P (Option Nat) := do
  let w ← get
  -- The lines come arguments first: the next one is for `q`'s first
  -- innermost application or literal.
  match q, w.atoms with
  | .app _ _, (_, h, cs) :: _ =>
    let (g, k) := firstLine q
    if g == h && cs.length == k then pure none
    else pure ((Pat.toTerm? q).bind (eval w.S))
  | .app _ _, [] => pure ((Pat.toTerm? q).bind (eval w.S))
  | _, _ => pure none

/-- The application pattern `f(ps)` against the next line, once each argument
that is no variable has its matched node and instance in `sub`. -/
def walkApp (key : String) (f : String) (ps : List Pat) (sub : List (Option (Nat × Nat))) :
    WalkM P (Nat × Nat) := do
  let w ← get
  match w.atoms with
  | (n, g, cs) :: rest =>
    let S := w.S
    if g != f || cs.length != ps.length then throw "rule: line for another application"
    let mut σ := w.σ
    let mut ic : Array Nat := #[]
    for (q, o, c) in ps.zip (sub.zip cs) do
      match q, o with
      | .var x, _ =>
        match σ.lookup x with
        | some y =>
          if S.fd y != S.fd c then throw "rule: variable bound twice"
          ic := ic.push y
        | none =>
          σ := (x, c) :: σ
          ic := ic.push c
      | _, some (m, i) =>
        if S.fd m != S.fd c then throw "rule: argument differs"
        ic := ic.push i
      | _, none => throw "rule: argument differs"
    match S.defOf n with
    | some (.app h ds) =>
      if h != f || (let (x, y) := nf2 S f ds cs; x != y) then throw "rule: matched node differs"
    | _ => throw "rule: matched node differs"
    set { w with atoms := rest, σ := σ }
    let i ← instOf f ic.toList n
    modify fun w => { w with memo := (key, n, i) :: w.memo }
    pure (n, i)
  | [] => throw "rule: no line for an application"

mutual

/-- The node the pattern `p` matched and its instance, consuming the firing's
`e` lines: arguments first, then the application's own line. -/
def walkQ (p : Pat) : WalkM P (Nat × Nat) :=
  match p with
  | .var x => do
    match (← get).σ.lookup x with
    | some n => pure (n, n)
    | none => throw "rule: unbound variable"
  | .lit s v => do
    let w ← get
    match w.atoms with
    | (n, "#lit", _) :: rest =>
      match w.S.defOf n with
      | some (.lit s' v') =>
        if s' == s && v' == v then set { w with atoms := rest }; pure (n, n)
        else throw "rule: literal differs"
      | _ => throw "rule: literal differs"
    | _ => throw "rule: no line for a literal"
  | .app f ps => walkQs ps >>= walkApp (key (.app f ps)) f ps

/-- The matched node and instance of each argument that is no variable. -/
def walkQs : List Pat → WalkM P (List (Option (Nat × Nat)))
  | [] => pure []
  | .var _ :: rest => walkQs rest >>= fun r => pure (none :: r)
  | .lit s v :: rest =>
    walkQ (.lit s v) >>= fun x => walkQs rest >>= fun r => pure (some x :: r)
  | .app f qs :: rest =>
    groundNode (.app f qs) >>= fun g =>
      (match g with
        | some n => letInstance (.app f qs) n >>= fun i => pure (n, i)
        | none => walkQ (.app f qs)) >>= fun x =>
      walkQs rest >>= fun r => pure (some x :: r)

end

/-- A `let` name's term on the right-hand side: the engine fetched the name's
node. The pattern is the name's term when the node is defined as that term,
argument for argument; otherwise the name is further down the pattern. -/
def letName? (p : Pat) : WalkM P (Option (Nat × Nat)) := do
  let w ← get
  if let (n, true) :: rest := w.rhs then
    if ((Pat.toTerm? p).map (denotes w.S n)).getD false then
      set { w with rhs := rest }
      return some (n, ← letInstance p n)
  return none

/-- The built application `f` of the built arguments `cs` against the next
`b` node. -/
def builtApp (f : String) (cs : List (Nat × Nat)) : WalkM P (Nat × Nat) := do
  let w ← get
  match w.rhs with
  | (n, _) :: rest =>
    if spells w.S n f (cs.map (·.1)) then
      set { w with rhs := rest }
      let i ← instOf f (cs.map (·.2)) n
      pure (n, i)
    else throw "rule: built node differs"
  | [] => throw "rule: no node for a built application"

mutual

/-- The node the pattern `p` was built as and its instance, consuming the
firing's `b` nodes. -/
def walkB (p : Pat) : WalkM P (Nat × Nat) :=
  match p with
  | .var x => do
    match (← get).σ.lookup x with
    | some n => pure (n, n)
    | none => throw "rule: unbound variable"
  | .lit s v => do
    if let some r ← letName? (.lit s v) then return r
    let w ← get
    match w.rhs with
    | (n, _) :: rest =>
      match w.S.defOf n with
      | some (.lit s' v') =>
        if s' == s && v' == v then set { w with rhs := rest }; pure (n, n)
        else throw "rule: built literal differs"
      | _ => throw "rule: built literal differs"
    | [] => throw "rule: no node for a built literal"
  | .app f ps =>
    letName? (.app f ps) >>= fun r =>
      match r with
      | some r => pure r
      | none => walkBs ps >>= builtApp f

def walkBs : List Pat → WalkM P (List (Nat × Nat))
  | [] => pure []
  | p :: ps => walkB p >>= fun x => walkBs ps >>= fun r => pure (x :: r)

end

/-- One side of a body equality: a bound variable's node, a matched pattern's
node and instance, or `none` for a variable not bound yet. -/
def side (p : Pat) : WalkM P (Option (Nat × Nat)) := do
  match p with
  | .var x => pure (((← get).σ.lookup x).map fun n => (n, n))
  | _ =>
    match (← get).memo.lookup (key p) with
    | some r => pure (some r)
    | none =>
      -- A ground side with no line of its own is a `let` name's term.
      let w ← get
      let (g, k) := firstLine p
      let hasLine := match w.atoms with
        | (_, h, cs) :: _ => g == h && cs.length == k
        | [] => false
      match hasLine, (Pat.toTerm? p).bind (eval w.S) with
      | false, some n => pure (some (n, ← letInstance p n))
      | _, _ => some <$> walkQ p

def bindVar (p : Pat) (n : Nat) : WalkM P Unit := do
  match p with
  | .var x => modify fun w => { w with σ := (x, n) :: w.σ }
  | _ => throw "rule: equality without a node"

/-- What a firing of rule `r` gives the kernel's `rule` step: the instances
of its two sides, the nodes they are, the assignment, and a step for each
body equality between the instances of its sides. -/
structure Fired where
  nl : Nat
  il : Nat
  nr : Nat
  ir : Nat
  σ : List (String × Nat)
  prems : Option (List Nat)

def fireRule (r : Rule) (rewrite : Bool) : WalkM P Fired := do
  let l? ← if rewrite then some <$> walkQ r.lhs else pure none
  for (p, q) in r.eqs do
    match ← side p, ← side q with
    | some (a, _), some (b, _) =>
      let S := (← get).S
      if S.fd a != S.fd b then throw "rule: body equality does not hold"
    | none, some (b, _) => bindVar p b
    | some (a, _), none => bindVar q a
    | none, none => throw "rule: equality without a node"
  let (nl, il) ← match l? with
    | some x => pure x
    | none => walkB r.lhs
  let (nr, ir) ← walkB r.rhs
  let w ← get
  for x in r.vars do
    match w.σ.lookup x, r.sorts.lookup x with
    | some n, some s => if sortOf w.S n != some s then throw "rule: variable of another sort"
    | _, _ => throw "rule: unbound variable"
  -- The body equalities, between instances: every pattern is matched by now.
  let mut prems : Option (Array Nat) := some #[]
  for (p, q) in r.eqs do
    match ← side p, ← side q with
    | some (_, ip), some (_, iq) =>
      let st ← withS fun S =>
        let (S, pf) := eqP S ip iq
        stepOf S ip pf
      prems := match prems, st with
        | some ps, some st => some (ps.push st)
        | _, _ => none
    | _, _ => prems := none
  pure { nl, il, nr, ir, σ := (← get).σ, prems := prems.map (·.toList) }

/-- The engine's node `i` is definition `d`. An id is defined once between
restores. -/
def define (S : St P) (i : Nat) (d : Def) : St P :=
  if (S.tr i).isSome then S.fail "definition: node already defined"
  else
    match intern S d with
    | (S, none) => S.fail "definition: ill-sorted"
    | (S, some t) =>
    let cid := if S.cid.size ≤ i then S.cid ++ Array.replicate (i + 1 - S.cid.size) none else S.cid
    let S := { S with cid := cid.setIfInBounds i (some t) }
    match d with
    | .lit s v => { S with lits := S.lits.insert (s, v) t }
    | _ => S

def stepCore (S : St P) (line : String) : St P :=
  let S := { S with events := S.events + 1, cur := (line.splitOn " ").headD "" }
  match line.splitOn " " with
  | "n" :: id :: f :: kids =>
    match id.toNat?, ids S kids with
    | some i, some cs => define S i (.app f cs)
    | _, _ => S.fail "definition: unreadable"
  | "l" :: id :: s :: rest =>
    match id.toNat? with
    | some i => define S i (.lit s (" ".intercalate rest))
    | none => S.fail "definition: unreadable"
  | "t" :: id :: f :: kids =>
    match S.node? id, ids S kids with
    | some i, some cs =>
      if spells S i f cs then termLine { S with spell := S.spell.insert (f, cs) i } i f cs
      else S.fail "term: its node differs"
    | _, _ => S.fail "term: unreadable"
  | ["s", c, m] =>
    match S.node? c, S.node? m with
    | some c, some m => { S with splices := (c, m) :: S.splices, events := S.events - 1 }
    | _, _ => S.fail "splice: unreadable"
  | ["z", f, u] =>
    match S.node? u, (S.prog.opDecl? f).bind (·.unit) with
    | some u, some t =>
      if denotes S u t then { S with units := S.units.insert f u, events := S.events - 1 }
      else S.fail "unit: its node differs"
    | _, _ => S.fail "unit: no such unit"
  | ["o"] => { (S.withCore fun c => (c.roundStart, ())).1 with events := S.events - 1 }
  | ["j", m] =>
    match S.node? m with
    | some m => { S with inverses := m :: S.inverses, events := S.events - 1 }
    | none => S.fail "inverse witness: unreadable"
  | ["x", off, a, b] =>
    match off.toNat?, S.node? a, S.node? b with
    | some o, some a, some b =>
      match S.declAt[o]? with
      | some (.axiom l r) =>
        if eval S l == some a && eval S r == some b then
          match writtenP S l with
          | (S, some (tl, _, pl)) =>
            match writtenP S r with
            | (S, some (tr, _, pr)) =>
              -- `a` is the left term, which the `union` equates to the right
              -- term, which is `b`.
              let (S, ax) := emit S (.axiom o tl tr) tl tr
              let (S, q1) := eqP S a tl
              let _ := pl
              let _ := pr
              let (S, q) := transP S a tr q1 (some (some ax))
              let (S, q2) := eqP S tr b
              let (S, q) := transP S a b q q2
              S.mergeBy a b q
            | (S, none) => S.merge a b
          | (S, none) => S.merge a b
        else S.fail "union: its terms differ"
      | _ => S.fail "union: no such command"
    | _, _, _ => S.fail "union: unreadable"
  | ["c", a, b] =>
    match S.node? a, S.node? b with
    | some a, some b =>
      match S.defOf a, S.defOf b with
      | some (.app f as), some (.app g bs) =>
        if f == g && (let (x, y) := nf2 S f as bs; x == y) then
          let (S, p) := congStepL S f a b
          S.mergeBy a b p
        else S.fail "congruence: arguments differ"
      | _, _ => S.fail "congruence: not two applications"
    | _, _ => S.fail "congruence: unreadable"
  | ["w", a, b] =>
    match S.node? a, S.node? b with
    | some a, some b =>
      -- Either node can be the application whose arguments normalize to the other.
      let one (x y : Nat) : Bool :=
        match S.defOf x with
        | some (.app f as) => spells S y f as
        | _ => false
      if one a b || one b a then
        let f := match S.defOf a, S.defOf b with
          | some (.app f as), _ => if spells S b f as then f else
              (match S.defOf b with | some (.app g _) => g | _ => f)
          | _, some (.app g _) => g
          | _, _ => ""
        let (S, p) := congStepL S f a b
        S.mergeBy a b p
      else match S.defOf a, S.defOf b with
        | some (.app _ _), _ | _, some (.app _ _) => S.fail "law: arguments differ"
        | _, _ => S.fail "law: not an application"
    | _, _ => S.fail "law: unreadable"
  | ["v", a, b, n1, n2] =>
    match S.node? a, S.node? b, S.node? n1, S.node? n2 with
    | some a, some b, some n1, some n2 =>
      match groupLaw S a b n1 n2 with
      | .ok () =>
        let (S, pf) := groupLawP S a b n1 n2
        S.mergeBy a b pf
      | .error e => S.fail e
    | _, _, _, _ => S.fail "group law: unreadable"
  | ["r", off, kind] =>
    match off.toNat? with
    | some o => { S with fire := some (o, kind == "w"), atoms := #[], rhs := [], events := S.events - 1 }
    | none => S.fail "rule: unreadable"
  | "e" :: id :: f :: kids =>
    match S.node? id, ids S kids with
    | some i, some cs => { S with atoms := S.atoms.push (i, f, cs), events := S.events - 1 }
    | _, _ => S.fail "rule: unreadable"
  | "b" :: xs =>
    let one (x : String) : Option (Nat × Bool) :=
      if x.startsWith "g" then (S.node? (x.drop 1).toString).map (·, true) else (S.node? x).map (·, false)
    match xs.mapM one with
    | some r => { S with rhs := r, events := S.events - 1 }
    | none => S.fail "rule: unreadable"
  | ["m", j, a, b] =>
    match j.toNat?, S.node? a, S.node? b, S.fire with
    | some j, some a, some b, some (o, rw) =>
      -- The engine cites a rule by an offset inside its command.
      match ((S.prog.decls.filter (·.1 ≤ o)).getLast? : Option (Nat × Decl)) with
      | some (od, Decl.rules rs) =>
        match rs[j]? with
        | some (some r) =>
          -- The walk takes the state and gives it back, whether it succeeds or not.
          let (atoms, rhs) := (S.atoms.toList, S.rhs)
          let (res, w) := ((fireRule r rw).run).run { S := S, atoms, rhs }
          let S := w.S
          match res with
          | .ok fr =>
            -- The instances have joined their nodes' classes, each with its
            -- own proof, and stay there if the merge fails.
            if (S.fd fr.nl == S.fd a && S.fd fr.nr == S.fd b) || (S.fd fr.nl == S.fd b && S.fd fr.nr == S.fd a)
            then
              -- `a` is the left instance, which the rule equates to the right
              -- instance, which is `b` (or the same with `a`, `b` exchanged).
              let (x, y) := if S.fd fr.nl == S.fd a then (a, b) else (b, a)
              let (S, pf) := match fr.prems with
                | some prems =>
                  let (S, st) := emit S (.rule od j fr.σ prems fr.il fr.ir) fr.il fr.ir
                  let (S, p1) := eqP S x fr.il
                  let (S, p2) := eqP S fr.ir y
                  let (S, q) := transP S x fr.ir p1 (some (some st))
                  transP S x y q p2
                | none => (S, none)
              S.mergeBy x y pf
            else S.fail "rule: merged nodes differ"
          | .error e => S.fail e
        | _ => S.fail "rule: outside the reader's language"
      | _ => S.fail "rule: no such command"
    | _, _, _, _ => S.fail "rule: unreadable"
  | ["g", off, a, b] =>
    match off.toNat?, S.node? a, S.node? b with
    | some o, some a, some b =>
      match S.declAt[o]? with
      | some (.goal l r) =>
        if eval S l == some a && eval S r == some b then
          if S.fd a == S.fd b then
            let S := { S with proved := o :: S.proved }
            -- The kernel's goal step: left term = `a` = `b` = right term.
            match writtenP S l with
            | (S, some (tl, _, _)) =>
              match writtenP S r with
              | (S, some (tr, _, _)) =>
                -- The terms have joined their nodes' classes.
                let (S, q) := eqP S tl tr
                match stepOf S tl q with
                | (S, some st) => (S.withCore fun c => c.goal o l r st).1
                | (S, none) => S
              | (S, none) => S
            | (S, none) => S
          else S.fail "goal: not in one class"
        else S.fail "goal: its terms differ"
      | _ => S.fail "goal: no such command"
    | _, _, _ => S.fail "goal: unreadable"
  | "i" :: a :: b :: n :: rest =>
    match S.node? a, S.node? b, S.node? n, (rest.mapM (fun (x : String) => x.toNat?)).bind (rules S) with
    | some a, some b, some n, some rs =>
      -- The derivation is computed first, on classes the state shares; the
      -- kernel steps are emitted after, when the state is held once again.
      match interReduce S S.atRound a b n rs with
      | .ok c =>
        let (S, r) := emitChain S c
        match r with
        | some (start, target, pf) =>
          -- The start is in the class of the merged node that is not the target.
          let other := if target == a then b else a
          let (S, q) := eqP S other start
          let (S, q) := transP S other target q pf
          S.mergeBy other target q
        | none => S.merge a b
      | .error e => S.fail e
    | _, _, _, _ => S.fail "completion: unreadable"
  | "p" :: a :: b :: rest =>
    match S.node? a, S.node? b, (rest.mapM (fun (x : String) => x.toNat?)).bind (Peak.read S) with
    | some a, some b, some w =>
      match peakMerge S S.atRound a b w with
      | .ok pl =>
        -- Both sides start at the peak's term.
        let (S, ra) := emitChain S pl.a
        let (S, rb) := emitChain S pl.b
        match ra, rb, pl.cancel with
        | some (start, ta, pa), some (_, tb, pb), none =>
          -- `a` is the peak's term, which is `b`.
          let (S, q) := symmP S start ta pa
          let (S, q) := transP S ta tb q pb
          S.mergeBy ta tb q
        | some (start, ta, pa), some (_, tb, pb), some (left, right, gone, ca, cb) =>
          -- Each side's monomial before the cancellation is `f(kept, lost)`;
          -- the two are equal, so the `cancel` step equates what they keep,
          -- and each side goes on from there.
          let f := pl.a.f
          let (S, nl) := monoNode S f left
          let (S, nr) := monoNode S f right
          let (S, ng) := monoNode S f gone
          match nl, nr, ng with
          | some nl, some nr, some ng =>
            if gone.isEmpty then
              -- Nothing is lost: the two sides are what they were.
              let (S, q) := symmP S start ta pa
              let (S, q) := transP S ta tb q pb
              let S := S.mergeBy ta tb q
              let (S, r1) := emitChain S ca
              let (S, r2) := emitChain S cb
              match r1, r2 with
              | some (_, _, _), some (_, _, _) => let (S, q) := eqP S a b; S.mergeBy a b q
              | _, _ => S.merge a b
            else
              let (S, la) := appNode S f [nl, ng]
              let (S, lb) := appNode S f [nr, ng]
              match la, lb with
              | some la, some lb =>
                let (S, p1) := congStepL S f la ta
                let (S, p2) := congStepL S f tb lb
                let (S, q) := symmP S start ta pa
                let (S, q) := transP S la start p1 q
                let (S, q) := transP S la tb q pb
                let (S, q) := transP S la lb q p2
                match stepOf S la q with
                | (S, some st) =>
                  let (S, c) := emit S (.cancel f st nl nr ng) nl nr
                  let S := S.mergeBy nl nr (some (some c))
                  let (S, _) := emitChain S ca
                  let (S, _) := emitChain S cb
                  let (S, q) := eqP S a b
                  S.mergeBy a b q
                | (S, none) => S.merge a b
              | _, _ => S.merge a b
          | _, _, _ => S.merge a b
        | _, _, _ => S.merge a b
      | .error e => S.fail e
    | _, _, _ => S.fail "completion: unreadable"
  | ["mark", d] =>
    match d.toNat? with
    | some (d + 1) =>
      let S := (S.withCore fun c => (c.mark d, ())).1
      { S with snaps := (S.snaps.extract 0 d).push (S.cid.size, S.plain, S.spell) }
    | _ => S.fail "mark: unreadable"
  | ["restore", d] =>
    match d.toNat? with
    | some (d + 1) =>
      match S.snaps[d]?, S.withCore fun c => c.restore d (d + 1) with
      | some (n, pl, sp), (S, true) =>
        -- The engine's ids past the mark are free again; the table keeps its
        -- nodes, and the kernel steps checked since stay true.
        { S with cid := S.cid.extract 0 n, plain := pl, spell := sp,
                 snaps := S.snaps.extract 0 (d + 1), fire := none }
      | _, (S, _) => S.fail "restore: no such mark"
    | _ => S.fail "restore: unreadable"
  | ["rpop", d] =>
    match d.toNat? with
    | some d =>
      match S.snaps[d]?, S.withCore fun c => c.restore d d with
      | some (n, pl, sp), (S, true) =>
        { S with cid := S.cid.extract 0 n, plain := pl, spell := sp,
                 snaps := S.snaps.extract 0 d, fire := none }
      | _, (S, _) => S.fail "restore: no such mark"
    | none => S.fail "restore: unreadable"
  | "u" :: kind :: rest =>
    -- An event the stream gives no witness for: counted, and nothing is merged.
    let _ := rest
    { S with unchecked := S.unchecked.insert kind (S.unchecked.getD kind 0 + 1), splices := [], inverses := [] }
  | [""] => { S with events := S.events - 1 }
  | _ => S.fail "unreadable line"

/-- Replays one line. The witness lines (`s`, `j`) hold until the next line
of another kind has been replayed. -/
def step (S : St P) (line : String) : St P :=
  let S := stepCore S line
  if line.startsWith "s " || line.startsWith "j " then S
  else { S with splices := [], inverses := [] }

def start (P : Program) : St P :=
  { declAt := P.decls.foldl (fun m (o, d) => m.insert o d) {} }

end SemperCheck.Replay

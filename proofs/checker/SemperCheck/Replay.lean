import SemperCheck.Parse
import SemperCheck.Kernel
import Std.Data.HashMap

/-!
# The replayer

Reads the engine's event stream in order (`proofs/checker/REPLAY.md`) and
checks each event against its own classes: a table of node definitions and a
union-find over node ids. A check is a fixed number of class lookups, a sort
of a node's arguments by class, or the instantiation of a pattern; none
searches.

This file is the executable replayer. It is not yet covered by a soundness
theorem: what it reports as proved is a measurement of the design, not a
checked proof.
-/

namespace SemperCheck.Replay

open SemperCheck

/-- What a node id stands for. -/
inductive Def where
  | lit (s v : String)
  | app (f : String) (args : List Nat)
  deriving Inhabited, BEq, Hashable

/-- The root of `i`'s class. A non-root's parent is a smaller id, so the walk
ends without a step count. -/
def find (parent : Array Nat) (i : Nat) : Nat :=
  match parent[i]? with
  | some p => if _h : p < i then find parent p else i
  | none => i
termination_by i

def grow (p : Array Nat) (n : Nat) : Array Nat := Id.run do
  let mut p := p
  for i in [p.size:n] do p := p.push i
  return p

/-- Merges the classes of `a` and `b`: the larger root points to the smaller. -/
def union (parent : Array Nat) (a b : Nat) : Array Nat :=
  let ra := find parent a
  let rb := find parent b
  if ra == rb then parent
  else
    let lo := min ra rb
    let hi := max ra rb
    (grow parent (hi + 1)).setIfInBounds hi lo

abbrev Spell := Std.HashMap (String × List Nat) Nat

structure St where
  P : Program
  declAt : Std.HashMap Nat Decl
  /-- The node table: every node the stream defined, each definition once.
  A table id is what the classes, the spelling table and every check use. -/
  defs : Array (Option Def) := #[]
  /-- The table id of each definition. -/
  index : Std.HashMap Def Nat := {}
  /-- The table id of each of the engine's node ids. A restore discards the
  engine's ids past the mark, and the engine reuses them; the table keeps its
  nodes. -/
  cid : Array (Option Nat) := #[]
  parent : Array Nat := #[]
  /-- The classes at the start of the completion round (`o` line): the round's
  merges are computed on them. They refine the current classes. -/
  roundParent : Array Nat := #[]
  /-- `(f, c1 .. ck) -> id`: the program term `f(c1 .. ck)` evaluated to `id`. -/
  spell : Spell := {}
  /-- The node of each operator's unit (`z` lines). -/
  units : Std.HashMap String Nat := {}
  /-- Each literal's node, checked against its definition on use. -/
  lits : Std.HashMap (String × String) Nat := {}
  /-- Each mark: the number of definitions, the classes and the spelling
  table at the mark. -/
  snaps : Array (Nat × Array Nat × Array (Option Nat) × Spell) := #[]
  /-- The kernel steps emitted so far, and what each concludes. The kernel
  (`Kernel.lean`, proved by `goal_sound`) checks them after the replay. -/
  steps : Array Step := #[]
  concl : Array (Nat × Nat) := #[]
  /-- For each node with a parent, the step that proves it equal to its
  parent, or `none` for a link the replayer has no kernel step for. -/
  proof : Array (Option Nat) := #[]
  roundProof : Array (Option Nat) := #[]
  /-- For a node, the last program term that evaluated to it: the term's
  table id and the proof that the term is the node. -/
  lastTerm : Std.HashMap Nat (Nat × Option (Option Nat)) := {}
  /-- For a program term's table id, the node it evaluated to and the proof. -/
  byTerm : Std.HashMap Nat (Nat × Option (Option Nat)) := {}
  /-- `(o, s)`: step `s` proves the `check-eq` at offset `o`. -/
  goalSteps : List (Nat × Nat) := []
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
  proved : List Nat := []
  events : Nat := 0
  failed : Std.HashMap String Nat := {}
  nFailed : Nat := 0
  lastCause : String := ""
  /-- Measurement only: apply the merges of `u` lines without a check, to
  tell a check that fails by itself from one that fails because an earlier
  merge was not applied. A goal proved this way is not proved. -/
  assume : Bool := false
  unchecked : Std.HashMap String Nat := {}

namespace St

def fd (S : St) (i : Nat) : Nat := find S.parent i

def defOf (S : St) (i : Nat) : Option Def := S.defs.getD i none

/-- The table id of the engine's node `i`. -/
def tr (S : St) (i : Nat) : Option Nat := S.cid.getD i none

def node? (S : St) (x : String) : Option Nat := x.toNat?.bind S.tr

def fail (S : St) (cause : String) : St :=
  { S with failed := S.failed.insert cause (S.failed.getD cause 0 + 1), nFailed := S.nFailed + 1, lastCause := cause,
           splices := [], inverses := [] }

end St

/-! ## Proofs

A proof that two nodes are equal is `none` (the replayer has no kernel step),
`some none` (they are one node), or `some (some s)` (step `s` concludes it). -/

abbrev Pf := Option (Option Nat)

def emit (S : St) (st : Step) (a b : Nat) : St × Nat :=
  -- The size is read first: reading it after the push would keep a second
  -- reference to the array and make the push copy it.
  let n := S.steps.size
  ({ S with steps := S.steps.push st, concl := S.concl.push (a, b) }, n)

/-- `x = y` from `x = y`'s reverse. -/
def symmP (S : St) (x y : Nat) : Pf → St × Pf
  | some (some s) => let (S, t) := emit S (.symm s) y x; (S, some (some t))
  | p => (S, p)

/-- `x = z` from `x = y` and `y = z`. -/
def transP (S : St) (x z : Nat) : Pf → Pf → St × Pf
  | some none, q => (S, q)
  | p, some none => (S, p)
  | some (some s), some (some t) => let (S, u) := emit S (.trans s t) x z; (S, some (some u))
  | _, _ => (S, none)

/-- A step that concludes `x = y`, a reflexivity when they are one node. -/
def stepOf (S : St) (x : Nat) : Pf → St × Option Nat
  | some (some s) => (S, some s)
  | some none => let (S, s) := emit S (.refl x) x x; (S, some s)
  | none => (S, none)

/-- The root of `i`'s class and the proof that `i` is it. -/
partial def findP (S : St) (i : Nat) : St × Nat × Pf :=
  match S.parent[i]? with
  | some p =>
    if p < i then
      let (S, r, q) := findP S p
      match S.proof.getD i none with
      | some s =>
        let (S, pf) := transP S i r (some (some s)) q
        -- Point `i` at its root, with the proof just composed.
        match pf with
        | some (some t) =>
          if r != p then
            ({ S with parent := S.parent.setIfInBounds i r,
                      proof := S.proof.setIfInBounds i (some t) }, r, pf)
          else (S, r, pf)
        | _ => (S, r, pf)
      | none => (S, r, none)
    else (S, i, some none)
  | none => (S, i, some none)

/-- The proof that `x` and `y`, of one class, are equal. -/
def eqP (S : St) (x y : Nat) : St × Pf :=
  if x == y then (S, some none)
  else
    let (S, rx, px) := findP S x
    let (S, ry, py) := findP S y
    if rx != ry then (S, none)
    else
      let (S, qy) := symmP S y ry py
      transP S x y px qy

/-- Merges the classes of `a` and `b`, which `pf` proves equal: the link
between the two roots carries the proof that they are. -/
def St.mergeBy (S : St) (a b : Nat) (pf : Pf) : St :=
  let (S, ra, pa) := findP S a
  let (S, rb, pb) := findP S b
  let S := { S with splices := [], inverses := [] }
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
    let S := if S.proof.size ≤ hi then
        { S with proof := S.proof ++ Array.replicate (hi + 1 - S.proof.size) none }
      else S
    let S := { S with parent := (grow S.parent (hi + 1)).setIfInBounds hi lo }
    { S with proof := S.proof.setIfInBounds hi (link.bind id) }

/-- A merge the replayer has no kernel step for. -/
def St.merge (S : St) (a b : Nat) : St := S.mergeBy a b none

/-- An associative operator's nested applications among `args`, spliced in as
the engine's term builder splices them before the arguments are built. -/
partial def flattenSyn (f : String) (args : List Term) : List Term :=
  args.flatMap fun
    | .app g xs => if g == f && !xs.isEmpty then flattenSyn f xs else [.app g xs]
    | t => [t]

/-- The node a program term evaluated to, through the spelling table. -/
partial def eval (S : St) : Term → Option Nat
  | .lit s v =>
    match S.lits[(s, v)]? with
    | some n =>
      match S.defOf n with
      | some (.lit s' v') => if s' == s && v' == v then some n else none
      | _ => none
    | none => none
  | .app f args => do
    let args := if S.P.kind f == .assoc then flattenSyn f args else args
    let ids ← args.mapM (eval S)
    S.spell[(f, ids)]?

/-- Node `n`'s definition is the term `t`, argument for argument. -/
partial def denotes (S : St) (n : Nat) : Term → Bool
  | .lit s v => match S.defOf n with
    | some (.lit s' v') => s' == s && v' == v
    | _ => false
  | .app f ts => match S.defOf n with
    | some (.app g cs) => g == f && cs.length == ts.length && (cs.zip ts).all fun (c, t) => denotes S c t
    | _ => false

/-- The node of `f`'s unit: the one a `z` line named, if its definition still
is the declared unit (a restore can have discarded it). -/
def St.unit (S : St) (f : String) : Option Nat :=
  match S.units[f]?, (S.P.opDecl? f).bind (·.unit) with
  | some u, some t => if denotes S u t then some u else none
  | _, _ => none

/-- The applications of `f` among `xs` and, literally nested, below them:
each is a splice witness for its own class. -/
def nested (defs : Array (Option Def)) (f : String) (x : Nat) : List (Nat × List Nat) :=
  match defs.getD x none with
  | some (.app g cs) =>
    if g == f && !cs.isEmpty then
      (x, cs) :: cs.flatMap fun c => if _h : c < x then nested defs f c else []
    else []
  | _ => []
termination_by x

/-- `a`, or the arguments a witness for `a`'s class splices in. A class is
not expanded inside its own expansion. -/
partial def expand (S : St) (W : List (Nat × List Nat)) (a : Nat) : List Nat :=
  let c := S.fd a
  match W.find? (·.1 == c) with
  | some (_, cs) => cs.flatMap (expand S (W.filter (·.1 != c)))
  | none => [a]

/-- Removes each argument that is `inv` applied to a node together with one
argument in that node's class; with `unit` given, also each argument that is
`inv` applied to a node of the unit's class. -/
def cancelInverse (S : St) (inv : String) (unit : Option Nat) (xs : List Nat) : List Nat := Id.run do
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
def nf2 (S : St) (f : String) (as bs : List Nat) (invUnit : Bool := false) : List Nat × List Nat :=
  match S.P.kind f with
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
    let d := S.P.opDecl? f
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
def spells (S : St) (n : Nat) (f : String) (cs : List Nat) : Bool :=
  -- The engine normalizes with and without `inv(e) = e`, at different events.
  [false, true].any fun invUnit =>
    (match S.defOf n with
      | some (.app g ds) => g == f && (let (x, y) := nf2 S f ds cs invUnit; x == y)
      | _ => false)
    || ((S.P.kind f).isAssoc &&
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
def lawReduce (S : St) (f : String) (atoms : List Nat) (inverse : Bool := true)
    (inverseFirst : Bool := false) : List Nat :=
  let d := S.P.opDecl? f
  let u := (S.unit f).map S.fd
  let dropUnit (xs : List Nat) : List Nat := xs.filter fun a => some (S.fd a) != u
  -- The engine drops the unit's arguments before it cancels inverse pairs,
  -- except in a group-law critical pair, whose peak holds the pair it cancels
  -- even when one of the two is in the unit's class (`inverseFirst`).
  let live : List Nat := match inverse, d.bind (fun d => d.inverse) with
    | true, some inv =>
      if inverseFirst then dropUnit (cancelInverse S inv none atoms)
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
  match S.P.kind f, d.bind (fun d => d.nilpotent) with
  | .aci, _ => keep fun _ => 1
  | _, some n => if n > 0 then keep (fun k => k % n) else live
  | _, none => live

/-- The classes of a monomial, sorted. -/
def classesOf (S : St) (atoms : List Nat) : List Nat := (atoms.map S.fd).mergeSort (· ≤ ·)

def countOf (c : Nat) (xs : List Nat) : Nat := (xs.filter (· == c)).length

/-- Removes `k` atoms of class `c`. -/
def dropClass (S : St) (c : Nat) : Nat → List Nat → List Nat
  | 0, xs => xs
  | _, [] => []
  | k + 1, x :: xs => if S.fd x == c then dropClass S c k xs else x :: dropClass S c (k + 1) xs

/-- The monomial `m` with the classes `l` replaced by the atoms `r`, as many
times as `m` holds `l` (once under ACI or a nilpotent law, where a class's
count is bounded, and once when `once` is set). `none` when `m` does not hold `l`. -/
def applyRule (S : St) (f : String) (m : List Nat) (l : List Nat) (r : List Nat) (once : Bool := false) :
    Option (List Nat) :=
  let mc := classesOf S m
  let distinct := l.eraseDups
  if l.isEmpty || !distinct.all (fun c => countOf c mc ≥ countOf c l) then none
  else
    let bounded := S.P.kind f == .aci || ((S.P.opDecl? f).bind (·.nilpotent)).isSome
    let q := if bounded || once then 1
      else distinct.foldl (fun q c => min q (countOf c mc / countOf c l)) (mc.length + 1)
    let rest := distinct.foldl (fun m c => dropClass S c (q * countOf c l) m) m
    -- Between rewrites the engine clamps counts and drops the unit; it cancels
    -- inverse pairs on the normal form only.
    some (lawReduce S f (rest ++ (List.replicate q r).flatten) (inverse := false))

/-- The arguments of `x` as a monomial of `f`: its own, if it is an
application of `f`, else `x` itself. -/
def monomial (S : St) (f : String) (W : List (Nat × List Nat)) (x : Nat) : List Nat :=
  -- A node that is one argument is still expanded when a witness splices its
  -- class: every list of one event reads a class the same way.
  match S.defOf x with
  | some (.app g cs) => if g == f && !cs.isEmpty then cs.flatMap (expand S W) else expand S W x
  | _ => expand S W x

/-- Rewrites `m` by the rules `rules`, in order. -/
def rewrite (S : St) (f : String) (W : List (Nat × List Nat)) (m : List Nat) (once : Bool := false) :
    List (Nat × Nat × Bool) → Except String (List Nat)
  | [] => pure m
  | (l, r, atom) :: rest => do
    if S.fd l != S.fd r then throw "completion: rule sides in two classes"
    match S.defOf l with
    | some (.app g ls) =>
      if g != f then throw "completion: rule of another operator"
      let lc := classesOf S (lawReduce S f (ls.flatMap (expand S W)))
      match applyRule S f m lc (if atom then [r] else monomial S f W r) once with
      | some m' => rewrite S f W m' once rest
      | none => throw "completion: rule does not apply"
    | _ => throw "completion: rule of another operator"

/-- The monomial `m` has the value of node `t`: it is `t`'s arguments, or it
is the one class of `t` (a result of one argument is that argument's class,
whose root can itself be an application of `f`). -/
def reaches (S : St) (f : String) (W : List (Nat × List Nat)) (m : List Nat) (t : Nat) : Bool :=
  let c := classesOf S (lawReduce S f m)
  c == classesOf S (lawReduce S f (monomial S f W t)) || c == [S.fd t]

/-- The splice witnesses a completion event shares: the applications of `f`
nested in the arguments of the nodes it names. -/
def lawWitnesses (S : St) (f : String) (nodes : List Nat) : List (Nat × List Nat) :=
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
def rules (S : St) (xs : List Nat) : Option (List (Nat × Nat × Bool)) :=
  (pairs xs).mapM fun (l, r, k) => do pure (← S.tr l, ← S.tr r, k)

/-- `i a b n l1 r1 ..`: node `n`, a member of one merged class, rewrites by
the rules to the other merged node. -/
def interReduce (S : St) (a b n : Nat) (rules : List (Nat × Nat × Bool)) : Except String Unit := do
  let some (.app f as) := S.defOf n | throw "completion: start is not an application"
  unless (S.P.kind f).isAssoc && S.P.kind f != .assoc do throw "completion: not an AC operator"
  let t ← if S.fd n == S.fd b then pure a else if S.fd n == S.fd a then pure b
    else throw "completion: start in neither class"
  -- A monomial is a node's arguments, each one class, as the engine reads it.
  let W : List (Nat × List Nat) := []
  let m ← rewrite S f W (lawReduce S f (as.flatMap (expand S W))) false rules
  unless reaches S f W m t do throw "completion: normal form differs"

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
def Peak.read (S : St) (xs : List Nat) : Option Peak := do
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
def peakMerge (S : St) (a b : Nat) (w : Peak) (inverseFirst : Bool := false) : Except String Unit := do
  let named := a :: b :: (w.preA ++ w.preB ++ w.postA ++ w.postB).flatMap fun (l, r, _) => [l, r]
  -- The operator: that of the first rule, else of a merged node.
  let some f := (named.reverse.findSome? fun x =>
      match S.defOf x with
      | some (.app g _) => if (S.P.kind g).isAssoc && S.P.kind g != .assoc then some g else none
      | _ => none)
    | throw "completion: no AC operator"
  -- A monomial is a node's arguments, each one class, as the engine reads it.
  let W : List (Nat × List Nat) := []
  let peak := w.peak.flatMap (expand S W)
  -- A critical pair's own rules rewrite the peak once each; the normal form's
  -- rules, after it, rewrite every copy.
  let mA ← rewrite S f W peak true w.preA
  let mB ← rewrite S f W (if w.reduceB then lawReduce S f peak (inverseFirst := inverseFirst) else peak)
    true w.preB
  let (mA, mB) ← if w.cancel then do
      -- Declared, or a consequence of the group laws (`:inverse`).
      unless ((S.P.opDecl? f).map fun d => d.cancellative || d.inverse.isSome).getD false do
        throw "completion: operator is not cancellative"
      let (mA, mB) := (lawReduce S f mA, lawReduce S f mB)
      let (ca, cb) := (classesOf S mA, classesOf S mB)
      let keep := w.keep.map S.fd
      -- The common part: each class, as many times as both sides hold it.
      let common := ca.eraseDups.map fun c =>
        (c, min (countOf c ca) (countOf c cb) - (if some c == keep then 1 else 0))
      let drop (m : List Nat) := common.foldl (fun m (c, k) => dropClass S c k m) m
      let (mA, mB) := (drop mA, drop mB)
      unless (!mA.isEmpty && !mB.isEmpty) || (S.unit f).isSome do
        throw "completion: cancellation empties a side"
      pure (mA, mB)
    else pure (mA, mB)
  let mA ← rewrite S f W mA false w.postA
  let mB ← rewrite S f W mB false w.postB
  unless reaches S f W mA a && reaches S f W mB b do throw "completion: normal form differs"

/-- `v a b n1 n2`: a consequence of the group law of an operator `f` with
`:inverse g`, where `n1 = g(x1)` and `n2 = g(x2)` (`n2` is `n1` when one node
is enough). One of:
- `g` is injective: `n1` and `n2` in one class give `x1 = x2`;
- `g(g(z)) = z`: `x1` in the class of `n2` gives `n1 = x2`;
- `g(x) = e` exactly when `x = e`;
- under `:nilpotent k`: `f(x1, .., x1) = n1` and `f(n1, .., n1) = x1`, with
  `k - 1` arguments. -/
def groupLaw (S : St) (a b n1 n2 : Nat) : Except String Unit := do
  let some (.app g [x1]) := S.defOf n1 | throw "group law: not an inverse node"
  let some (.app g' [x2]) := S.defOf n2 | throw "group law: not an inverse node"
  let some d := S.P.ops.find? (fun d => d.inverse == some g && (d.kind == .ac || d.kind == .aci))
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
def ids (S : St) (xs : List String) : Option (List Nat) := do
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
partial def kview (S : St) (f : String) (x : Nat) : List Nat :=
  match S.defOf x with
  | some (.app g cs) => if g == f && !cs.isEmpty then cs.flatMap (kview S f) else [x]
  | _ => [x]

/-- A `cong` step that concludes `a = b` for two nodes whose arguments the
replayer found equal as classes under `f`'s laws: its premises prove each
differing pair of arguments equal (plain and commutative operators), or send
each flattened argument to one node of its class, the unit's node for the
unit's class and the splice witness for a spliced class (associative
operators). `none` when a premise has no proof or the kernel's reading of the
two sides would differ. -/
def congStep (S : St) (f : String) (a b : Nat) : St × Pf := Id.run do
  if a == b then return (S, some none)
  let mut S := S
  let kind := S.P.kind f
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

/-- The table id of a program term as the kernel interns it: child for child. -/
partial def internT (S : St) : Term → Option Nat
  | .lit s v => S.index[Def.lit s v]?
  | .app f args => (args.mapM (internT S)).bind fun cs => S.index[Def.app f cs]?

/-- The proof that the program term `t`, of table id `w`, is node `a`: the
one its `t` line recorded, when the term evaluated to `a`. -/
def termP (S : St) (w a : Nat) : St × Pf :=
  if w == a then (S, some none)
  else match S.byTerm[w]? with
    | some (n, p) =>
      let (S, q) := eqP S n a
      transP S w a p q
    | none => (S, none)

/-! ## One line -/

def sortOf (S : St) (t : Nat) : Option String :=
  match S.defOf t with
  | some (.lit s _) => some s
  | some (.app f _) => (S.P.opDecl? f).map (·.res)
  | none => none

/-- The definition is well-sorted, as the kernel requires of every node. -/
def wellSorted (S : St) : Def → Bool
  | .lit s _ => S.P.litSorts.contains s
  | .app f cs =>
    match S.P.opDecl? f with
    | none => false
    | some d =>
      if d.kind.isAssoc then
        cs.all (fun c => sortOf S c == some d.res) && (!cs.isEmpty || d.unit.isSome)
      else cs.length == d.args.length && (cs.zip d.args).all fun (c, s) => sortOf S c == some s

/-- The table id of definition `d`, added to the table if it is new. -/
def intern (S : St) (d : Def) : St × Nat :=
  match S.index[d]? with
  | some t => (S, t)
  | none =>
    let t := S.defs.size
    ({ S with defs := S.defs.push (some d), index := S.index.insert d t }, t)

/-- The kernel steps of a `t` line, whose check passed: the term as the
program writes it (its arguments' own terms as arguments) is node `i`. -/
def termLine (S : St) (i : Nat) (f : String) (cs : List Nat) : St := Id.run do
  let done (S : St) : St := { S with splices := [], inverses := [] }
  let ws := cs.map fun c => ((S.lastTerm[c]?).map (·.1)).getD c
  let (dW, dT) := (Def.app f ws, Def.app f cs)
  if !(wellSorted S dW && wellSorted S dT) then return done S
  let (S, w) := intern S dW
  let (S, t2) := intern S dT
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
  let (S', p2) := congStep S f t2 i
  S := (S'.mergeBy t2 i p2).mergeBy w t2 p1
  let (S', p) := transP S w i p1 p2
  return { S' with lastTerm := S'.lastTerm.insert i (w, p), byTerm := S'.byTerm.insert w (i, p) }



/-! ## A rule firing

The walk matches the rule's patterns against the firing's lines, as before,
and builds what the kernel's `rule` step needs: the node of each pattern
instantiated by the assignment, and the proof that this instance is the node
the pattern matched or was built as. An instance joins that node's class. -/

structure Walk where
  S : St
  σ : List (String × Nat) := []
  atoms : List (Nat × String × List Nat)
  rhs : List (Nat × Bool)
  /-- The matched node and the instance of each matched pattern, by the
  pattern's printed form. -/
  memo : List (String × Nat × Nat) := []

/-- The walk keeps its state when it fails: the replayer's state is in it,
and is held by one reference at a time so that its arrays are updated in
place. -/
abbrev WalkM := ExceptT String (StateM Walk)

def St.empty : St := { P := { ops := [], litSorts := [], decls := [] }, declAt := {} }

/-- Runs `k` on the replayer's state, taken out of the walk while `k` runs. -/
def withS {α : Type} (k : St → St × α) : WalkM α :=
  modifyGet fun w =>
    let S := w.S
    let w := { w with S := St.empty }
    let (S, a) := k S
    (a, { w with S := S })

def key (p : Pat) : String := toString (repr p)

partial def Pat.toTerm? : Pat → Option Term
  | .var _ => none
  | .lit s v => some (.lit s v)
  | .app f ps => (ps.mapM Pat.toTerm?).map (.app f)

/-- The instance `f(ic)` of an application pattern, joined to node `n`. -/
def instOf (f : String) (ic : List Nat) (n : Nat) : WalkM Nat := do
  let d := Def.app f ic
  unless wellSorted (← get).S d do throw "rule: instance ill-sorted"
  withS fun S =>
    let (S, i) := intern S d
    let (S, p) := congStep S f i n
    (S.mergeBy i n p, i)

/-- A ground pattern that stands for a `let` name's term: its instance is
the term as the kernel interns it, joined to the name's node `n`. -/
def letInstance (p : Pat) (n : Nat) : WalkM Nat := do
  match (Pat.toTerm? p).bind (internT (← get).S) with
  | some t =>
    withS fun S =>
      let (S, pf) := termP S t n
      (S.mergeBy t n pf, t)
  | none => pure n

/-- The node the pattern `p` matched and its instance, consuming the firing's
`e` lines: arguments first, then the application's own line. -/
partial def walkQ (p : Pat) : WalkM (Nat × Nat) := do
  match p with
  | .var x =>
    match (← get).σ.lookup x with
    | some n => pure (n, n)
    | none => throw "rule: unbound variable"
  | .lit s v =>
    let w ← get
    match w.atoms with
    | (n, "#lit", _) :: rest =>
      match w.S.defOf n with
      | some (.lit s' v') =>
        if s' == s && v' == v then set { w with atoms := rest }; pure (n, n)
        else throw "rule: literal differs"
      | _ => throw "rule: literal differs"
    | _ => throw "rule: no line for a literal"
  | .app f ps =>
    -- A ground argument the next line does not match is a `let` name's term:
    -- the engine bound it to the name's node and wrote no line for it.
    let groundNode (q : Pat) : WalkM (Option Nat) := do
      let w ← get
      match q, w.atoms with
      | .app g qs, (_, h, cs) :: _ =>
        if g == h && cs.length == qs.length then pure none
        else pure ((Pat.toTerm? q).bind (eval w.S))
      | .app _ _, [] => pure ((Pat.toTerm? q).bind (eval w.S))
      | _, _ => pure none
    let mut sub : Array (Option (Nat × Nat)) := #[]
    for q in ps do
      match q with
      | .var _ => sub := sub.push none
      | _ =>
        match ← groundNode q with
        | some n => sub := sub.push (some (n, ← letInstance q n))
        | none => sub := sub.push (some (← walkQ q))
    let w ← get
    match w.atoms with
    | (n, g, cs) :: rest =>
      let S := w.S
      if g != f || cs.length != ps.length then throw "rule: line for another application"
      let mut σ := w.σ
      let mut ic : Array Nat := #[]
      for (q, o, c) in ps.zip (sub.toList.zip cs) do
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
      modify fun w => { w with memo := (key p, n, i) :: w.memo }
      pure (n, i)
    | [] => throw "rule: no line for an application"

/-- The node the pattern `p` was built as and its instance, consuming the
firing's `b` nodes. -/
partial def walkB (p : Pat) : WalkM (Nat × Nat) := do
  match p with
  | .var x =>
    match (← get).σ.lookup x with
    | some n => pure (n, n)
    | none => throw "rule: unbound variable"
  | _ =>
    let w ← get
    -- A `let` name's term: the engine fetched the name's node.
    if let (n, true) :: rest := w.rhs then
      match (Pat.toTerm? p).bind (eval w.S) with
      | some m =>
        if w.S.fd m == w.S.fd n then
          set { w with rhs := rest }
          return (n, ← letInstance p n)
        else throw "rule: let name differs"
      | none => throw "rule: let name differs"
    match p with
    | .lit s v =>
      match w.rhs with
      | (n, _) :: rest =>
        match w.S.defOf n with
        | some (.lit s' v') =>
          if s' == s && v' == v then set { w with rhs := rest }; pure (n, n)
          else throw "rule: built literal differs"
        | _ => throw "rule: built literal differs"
      | [] => throw "rule: no node for a built literal"
    | .app f ps =>
      let cs ← ps.mapM walkB
      let w ← get
      match w.rhs with
      | (n, _) :: rest =>
        if spells w.S n f (cs.map (·.1)) then
          set { w with rhs := rest }
          let i ← instOf f (cs.map (·.2)) n
          pure (n, i)
        else throw "rule: built node differs"
      | [] => throw "rule: no node for a built application"
    | .var _ => throw "rule: unbound variable"

/-- One side of a body equality: a bound variable's node, a matched pattern's
node and instance, or `none` for a variable not bound yet. -/
def side (p : Pat) : WalkM (Option (Nat × Nat)) := do
  match p with
  | .var x => pure (((← get).σ.lookup x).map fun n => (n, n))
  | _ =>
    match (← get).memo.lookup (key p) with
    | some r => pure (some r)
    | none => some <$> walkQ p

def bindVar (p : Pat) (n : Nat) : WalkM Unit := do
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

def fireRule (r : Rule) (rewrite : Bool) : WalkM Fired := do
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
def define (S : St) (i : Nat) (d : Def) : St :=
  if (S.tr i).isSome then S.fail "definition: node already defined"
  else if !wellSorted S d then S.fail "definition: ill-sorted"
  else
    let (S, t) := intern S d
    let cid := if S.cid.size ≤ i then S.cid ++ Array.replicate (i + 1 - S.cid.size) none else S.cid
    let S := { S with cid := cid.setIfInBounds i (some t) }
    match d with
    | .lit s v => { S with lits := S.lits.insert (s, v) t }
    | _ => S

def step (S : St) (line : String) : St :=
  let S := { S with events := S.events + 1 }
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
    match S.node? u, (S.P.opDecl? f).bind (·.unit) with
    | some u, some t =>
      if denotes S u t then { S with units := S.units.insert f u, events := S.events - 1 }
      else S.fail "unit: its node differs"
    | _, _ => S.fail "unit: no such unit"
  | ["o"] => { S with roundParent := S.parent, roundProof := S.proof, events := S.events - 1 }
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
          match internT S l, internT S r with
          | some tl, some tr =>
            -- `a` is the left term, which the `union` equates to the right
            -- term, which is `b`.
            let (S, ax) := emit S (.axiom o tl tr) tl tr
            let (S, pl) := termP S tl a
            let (S, pr) := termP S tr b
            let (S, q) := symmP S tl a pl
            let (S, q) := transP S a tr q (some (some ax))
            let (S, q) := transP S a b q pr
            S.mergeBy a b q
          | _, _ => S.merge a b
        else S.fail "union: its terms differ"
      | _ => S.fail "union: no such command"
    | _, _, _ => S.fail "union: unreadable"
  | ["c", a, b] =>
    match S.node? a, S.node? b with
    | some a, some b =>
      match S.defOf a, S.defOf b with
      | some (.app f as), some (.app g bs) =>
        if f == g && (let (x, y) := nf2 S f as bs; x == y) then
          let (S, p) := congStep S f a b
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
        let (S, p) := congStep S f a b
        S.mergeBy a b p
      else match S.defOf a, S.defOf b with
        | some (.app _ _), _ | _, some (.app _ _) => S.fail "law: arguments differ"
        | _, _ => S.fail "law: not an application"
    | _, _ => S.fail "law: unreadable"
  | ["v", a, b, n1, n2] =>
    match S.node? a, S.node? b, S.node? n1, S.node? n2 with
    | some a, some b, some n1, some n2 =>
      match groupLaw S a b n1 n2 with
      | .ok () => S.merge a b
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
      match ((S.P.decls.filter (·.1 ≤ o)).getLast? : Option (Nat × Decl)) with
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
            match internT S l, internT S r with
            | some tl, some tr =>
              let (S, pl) := termP S tl a
              let (S, pab) := eqP S a b
              let (S, pr) := termP S tr b
              let (S, qr) := symmP S tr b pr
              let (S, q) := transP S tl b pl pab
              let (S, q) := transP S tl tr q qr
              match stepOf S tl q with
              | (S, some st) => { S with goalSteps := (o, st) :: S.goalSteps }
              | (S, none) => S
            | _, _ => S
          else S.fail "goal: not in one class"
        else S.fail "goal: its terms differ"
      | _ => S.fail "goal: no such command"
    | _, _, _ => S.fail "goal: unreadable"
  | "i" :: a :: b :: n :: rest =>
    match S.node? a, S.node? b, S.node? n, (rest.mapM (fun (x : String) => x.toNat?)).bind (rules S) with
    | some a, some b, some n, some rs =>
      -- On the current classes, else on the classes at the round's start: the
      -- engine reads a round's monomials through the latter, and builds the
      -- nodes it merges through the former. Either check is sound.
      match interReduce S a b n rs, interReduce { S with parent := S.roundParent } a b n rs with
      | .ok (), _ | _, .ok () => S.merge a b
      | .error e, _ => S.fail e
    | _, _, _, _ => S.fail "completion: unreadable"
  | "p" :: a :: b :: rest =>
    match S.node? a, S.node? b, (rest.mapM (fun (x : String) => x.toNat?)).bind (Peak.read S) with
    | some a, some b, some w =>
      let R := { S with parent := S.roundParent }
      let tries := [peakMerge S a b w, peakMerge S a b w (inverseFirst := true),
                    peakMerge R a b w, peakMerge R a b w (inverseFirst := true)]
      if tries.any (fun t => t.isOk) then S.merge a b
      else match tries.head? with
        | some (.error e) => S.fail e
        | _ => S.fail "completion: unreadable"
    | _, _, _ => S.fail "completion: unreadable"
  | ["mark", d] =>
    match d.toNat? with
    | some (d + 1) => { S with snaps := (S.snaps.extract 0 d).push (S.cid.size, S.parent, S.proof, S.spell) }
    | _ => S.fail "mark: unreadable"
  | ["restore", d] =>
    match d.toNat? with
    | some (d + 1) =>
      match S.snaps[d]? with
      | some (n, p, pf, sp) =>
        -- The engine's ids past the mark are free again; the table keeps its
        -- nodes, and the kernel steps emitted since stay true.
        { S with cid := S.cid.extract 0 n, parent := p, proof := pf, spell := sp, roundParent := p,
                 roundProof := pf,
                 snaps := S.snaps.extract 0 (d + 1), fire := none }
      | none => S.fail "restore: no such mark"
    | _ => S.fail "restore: unreadable"
  | ["rpop", d] =>
    match d.toNat? with
    | some d =>
      match S.snaps[d]? with
      | some (n, p, pf, sp) =>
        { S with cid := S.cid.extract 0 n, parent := p, proof := pf, spell := sp, roundParent := p,
                 roundProof := pf,
                 snaps := S.snaps.extract 0 d, fire := none }
      | none => S.fail "restore: no such mark"
    | none => S.fail "restore: unreadable"
  | "u" :: kind :: rest =>
    let S := { S with unchecked := S.unchecked.insert kind (S.unchecked.getD kind 0 + 1), splices := [], inverses := [] }
    match S.assume, rest with
    | true, [a, b] =>
      match S.node? a, S.node? b with
      | some a, some b => S.merge a b
      | _, _ => S
    | _, _ => S
  | [""] => { S with events := S.events - 1 }
  | _ => S.fail "unreadable line"

def start (P : Program) : St :=
  { P, declAt := P.decls.foldl (fun m (o, d) => m.insert o d) {} }

end SemperCheck.Replay

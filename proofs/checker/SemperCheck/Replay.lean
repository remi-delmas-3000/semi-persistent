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
  snaps : Array (Nat × Array (Option Nat) × Spell × Std.HashMap Nat (List Nat)) := #[]
  /-- The operators that are some operator's `:inverse`. -/
  invOps : List String := []
  /-- For a class's root, the applications of an inverse operator the class
  holds: a class with `g(x)` in it cancels against the class of `x`. -/
  invIn : Std.HashMap Nat (List Nat) := {}
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
  /-- The witnesses of the open firing's `:flatten` matches, in the stream's
  order, each with the position `k` of the `e` line it belongs to. An opening
  (`s c m k p at`): a class `c` among the arguments the match reads, and the
  application `m` in that class whose arguments it reads in its place; `p` is
  the position, among the `e` line's openings, of the one whose member holds
  that argument, and `-` for an argument of the matched node itself; `at` is
  the number of arguments the match had read before `m`'s. A
  regrouping (`y c m k`): a pattern argument bound to class `c`, and the
  application `m` in that class whose arguments the node holds in its place. -/
  opens : List (Nat × Nat × Nat × Option Nat × Nat) := []
  regroups : List (Nat × Nat × Nat) := []
  /-- The binding lines (`q..`) of the sequence rule firing being read. -/
  seqLines : List (List String) := []
  /-- Inverse witnesses (`j` lines) for the next line: inverse applications,
  each standing for its class. -/
  inverses : List Nat := []
  /-- The open firing: its command's offset, and whether it is a `rewrite`. -/
  fire : Option (Nat × Bool) := none
  /-- The firing's `e` lines: the matched node, the operator, the nodes the
  argument patterns are bound to, each with its count, and, for each rest
  variable, its nodes. -/
  atoms : Array (Nat × String × List (Nat × Nat) × List (List Nat)) := #[]
  /-- The right-hand side's nodes; `true` marks a `let` name's node. -/
  rhs : List (Nat × Bool) := []
  /-- The `check-eq` whose two nodes were in one class at their `g` line. -/
  proved : List Nat := []
  events : Nat := 0
  failed : Std.HashMap String Nat := {}
  nFailed : Nat := 0
  lastCause : String := ""
  /-- With `logFailed`, every failed event: its number, cause and line. -/
  logFailed : Bool := false
  failedLog : Array String := #[]
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
  -- A cause can carry a detail after ` | `, which is shown and not counted by.
  let key := (cause.splitOn " | ").headD cause
  { S with failed := S.failed.insert key (S.failed.getD key 0 + 1), nFailed := S.nFailed + 1, lastCause := cause,
           splices := [], opens := [], regroups := [], inverses := [] }

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
        let S := match S.invIn[hi]? with
          | some xs => { S with invIn := (S.invIn.erase hi).insert lo (xs ++ S.invIn.getD lo []) }
          | none => S
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

/-- As `eval`, with no nested application read through: the node of a term
whose nested applications are `let` names, each standing for its class. -/
def evalN (S : St P) : Term → Option Nat
  | .lit s v => eval S (.lit s v)
  | .app f args => (evalNs S args).bind fun ids => S.spell[(f, ids)]?

def evalNs (S : St P) : List Term → Option (List Nat)
  | [] => some []
  | t :: ts => (evalN S t).bind fun a => (evalNs S ts).map (a :: ·)

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
  let inverseOf (a : Nat) : List Nat :=
    let arg (m : Nat) : Option Nat :=
      match S.defOf m with
      | some (.app g [y]) => if g == inv then some y else none
      | _ => none
    (arg a).toList ++ (S.inverses.filterMap fun m => if S.fd m == S.fd a then arg m else none)
      ++ (S.invIn.getD (S.fd a) []).filterMap arg
  let mut out := xs.toArray
  for a in xs do
    if let some i := out.findIdx? (· == a) then
      let rest := out.eraseIdxIfInBounds i
      -- The first of these that has what it cancels with: `inv(e)` is `e`
      -- and, with `unit` given, goes by itself; else an argument of the
      -- class it is the inverse of.
      let pick := (inverseOf a).findSome? fun y =>
        if unit == some (S.fd y) then some rest
        else (rest.findIdx? (fun b => S.fd b == S.fd y)).map rest.eraseIdxIfInBounds
      if let some r := pick then out := r
  return out.toList

/-- Sorted classes with each class's count reduced modulo `n`. -/
def modCount (n : Nat) (xs : List Nat) : List Nat :=
  let groups := xs.foldl (fun (acc : List (Nat × Nat)) c =>
    match acc with
    | (d, k) :: rest => if d == c then (d, k + 1) :: rest else (c, 1) :: acc
    | [] => [(c, 1)]) []
  groups.reverse.flatMap fun (c, k) => List.replicate (k % n) c

/-- The normal forms, as classes, of the argument lists `as` and `bs` of `f`.
An associative operator's argument is one class unless a witness of the
stream splices it (`s` lines, checked here): an application of `f` among the
arguments stands for its class when no line says the engine read through it.
Both lists use the same witnesses. -/
def nf2 (S : St P) (f : String) (as bs : List Nat) (invUnit : Bool := false)
    (self : Option Nat := none) : List Nat × List Nat :=
  match S.prog.kind f with
  | .plain => (as.map S.fd, bs.map S.fd)
  | .comm => ((as.map S.fd).mergeSort (· ≤ ·), (bs.map S.fd).mergeSort (· ≤ ·))
  | k =>
    let given := S.splices.filterMap fun (c, m) =>
      match S.defOf m with
      | some (.app g cs) => if g == f && !cs.isEmpty && S.fd m == S.fd c then some (S.fd c, cs) else none
      | _ => none
    -- The node whose arguments are `as` witnesses its own class: a rule with
    -- `:flatten` matches it through an argument of that class.
    let W := given ++ (match self with | some n => [(S.fd n, as)] | none => [])
    let u := (S.unit f).map S.fd
    let d := S.prog.opDecl? f
    let one (xs : List Nat) : List Nat :=
      -- The unit's arguments go first, as in the engine: `f(e, inv(e))` is
      -- `inv(e)`, which is in `e`'s class only once that is derived.
      -- An argument of the unit's class goes before it is read as its own
      -- arguments.
      let atoms := ((xs.filter fun a => some (S.fd a) != u).flatMap (expand S W)).filter
        fun a => some (S.fd a) != u
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

/-- The table's application of `f` to the arguments `m`, in the table's
order, if it holds one. -/
def nodeOfArgs (S : St P) (f : String) (m : List Nat) : Option Nat :=
  if m.isEmpty then none else S.index[Node.app f (m.mergeSort (· ≤ ·))]?

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
        -- The unit dropped and nothing else: the one argument left is the node.
        ((nf2 S f cs [] false).1 == [S.fd n] ||
        (let t := (nf2 S f cs [] invUnit).1
         -- One class left: the application is that class. None left: it is the unit.
         t == [S.fd n] || (t.isEmpty && (S.unit f).map S.fd == some (S.fd n)) ||
         -- The normal form is the argument list of a node of `n`'s class.
         (match nodeOfArgs S f t with
           | some x => S.fd x == S.fd n
           | none => false))))

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
def rewriteR (now S : St P) (f : String) (W : List (Nat × List Nat)) (m : List Nat) (once : Bool)
    (done : Array Rewrote) (raw : Option (List Nat)) :
    List (Nat × Nat × Bool) → Except String (List Nat × Array Rewrote)
  | [] => pure (m, done)
  | (l, r, atom) :: rest => do
    if now.fd l != now.fd r then throw "completion: rule sides in two classes"
    match S.defOf l with
    | some (.app g ls) =>
      if g != f then throw "completion: rule of another operator"
      -- A rule's left side keeps its inverse pairs: the engine cancels them on
      -- a normal form only.
      let lc := classesOf S (lawReduce S f (ls.flatMap (expand S W)) (inverse := false))
      -- The rule applies to the monomial as the laws left it, or to what the
      -- last rewrite gave before the laws clamped its counts (`raw`): the
      -- engine applies some rules before it clamps.
      let rr := if atom then [r] else monomial S f W r
      let hit := match applyRule S f m lc rr once, raw with
        | some x, _ => some x
        | none, some m0 => applyRule S f m0 lc rr once
        | none, none => none
      match hit with
      | some (q, left, m') =>
        rewriteR now S f W m' once (done.push { l, r, q, rest := left, after := m', atom })
          (some (left ++ (List.replicate q rr).flatten)) rest
      | none => throw s!"completion: rule does not apply | rule {done.size}: left side {ls} as classes {lc}, monomial {m} as classes {classesOf S m}"
    | _ => throw "completion: rule of another operator"

/-- `rewriteR` from a monomial the laws have reduced. -/
def rewrite (now S : St P) (f : String) (W : List (Nat × List Nat)) (m : List Nat) (once : Bool := false)
    (done : Array Rewrote := #[]) (rules : List (Nat × Nat × Bool)) :
    Except String (List Nat × Array Rewrote) :=
  rewriteR now S f W m once done none rules

/-- `y` is the unit's node, or an application of `f` in the unit's class. -/
def unitLike (S : St P) (f : String) (y : Nat) : Bool :=
  match S.unit f with
  | some u => y == u || (S.fd y == S.fd u && (match S.defOf y with
      | some (.app g _) => g == f
      | _ => false))
  | none => false

/-- The monomial `m` has the value of node `t`: it is `t`'s arguments, or it
is the one class of `t` (a result of one argument is that argument's class,
whose root can itself be an application of `f`). -/
def reaches (S : St P) (f : String) (W : List (Nat × List Nat)) (m : List Nat) (t : Nat) : Bool :=
  let c := classesOf S (lawReduce S f m)
  c == classesOf S (lawReduce S f (monomial S f W t)) || c == [S.fd t] ||
    -- The engine builds the node of the result: when the table holds the
    -- application of `f` to these arguments, the result is that node's class.
    -- The node is looked up before inverse pairs are cancelled, and with the
    -- arguments of the unit's class that are no application of `f` kept: the
    -- replayer can hold such an argument in the unit's class before the
    -- engine does.
    (match nodeOfArgs S f (lawReduce S f m (inverse := false)) with
      | some x => S.fd x == S.fd t
      | none => false) ||
    (match nodeOfArgs S f (m.filter fun y => !(unitLike S f y)) with
      | some x => S.fd x == S.fd t
      | none => false)

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
  unless reaches S f W m t do
    throw s!"completion: normal form differs | {m} as classes {classesOf S (lawReduce S f m)}"
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
    -- The two sides as the rewrites leave them: inverse pairs are cancelled
    -- on a normal form only.
    let (mA, mB) := (lawReduce R f mA (inverse := false), lawReduce R f mB (inverse := false))
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
    unless reaches S f W mA' a && reaches S f W mB' b do
      throw s!"completion: normal form differs | after cancellation: left {left} right {right}, side A {mA'} as classes {classesOf S (lawReduce S f mA')}, side B {mB'} as classes {classesOf S (lawReduce S f mB')}, without inverse cancellation {lawReduce S f mB' (inverse := false)} roots {(lawReduce S f mB' (inverse := false)).map S.fd}"
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
    unless reaches S f W mA a && reaches S f W mB b do
      throw s!"completion: normal form differs | side A {mA} as classes {classesOf S (lawReduce S f mA)}, side B {mB} as classes {classesOf S (lawReduce S f mB)}"
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

/-- `c` and `c:k` fields as nodes with their counts. -/
def idsC (S : St P) (xs : List String) : Option (List (Nat × Nat)) :=
  xs.mapM fun x =>
    match x.splitOn ":" with
    | [n] => (S.node? n).map (·, 1)
    | [n, k] => (S.node? n).bind fun n => k.toNat?.bind fun k => if k == 0 then none else some (n, k)
    | _ => none

/-- The node that is `f` applied to counted children: the children repeated
up to the kernel's `countLimit`, a counted application above it. -/
def countedNode (f : String) (cks : List (Nat × Nat)) : Node :=
  if cks.all (fun ck => ck.2 ≤ Ctx.countLimit) then .app f (Ctx.spread cks) else .napp f cks

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

/-- A witness of one `e` line: its position among the line's openings, the
class, the member, the opening it lies under (`none`: the node's own
arguments) and the number of arguments read before the member's. A regrouping
has no position that matters, lies under none and has no such number. -/
abbrev Wit := Nat × Nat × Nat × Option Nat × Nat

/-- The openings and the regroupings of the `e` line at position `k`. -/
def witsOf (S : St P) (k : Nat) : List Wit × List Wit :=
  (((S.opens.filter (·.1 == k)).map (·.2)).zipIdx.map fun ((c, m, p, at_), i) => (i, c, m, p, at_),
   ((S.regroups.filter (·.1 == k)).map (·.2)).zipIdx.map fun ((c, m), i) => (i, c, m, none, 0))

/-- Witness `w` reads argument `a`, which lies under the opening `ctx` after
`off` arguments read: `a` is in its class, its member is an application of `f`
in that class and, for an opening (`tree`), it lies under `ctx` too and, in a
sequence (`off` given), starts at `off`. -/
def Wit.reads (S : St P) (f : String) (tree : Bool) (ctx : Option Nat) (off : Option Nat) (a : Nat)
    (w : Wit) : Bool :=
  S.fd w.2.1 == S.fd a && S.fd w.2.2.1 == S.fd a && (!tree || w.2.2.2.1 == ctx) &&
    (!tree || off.all (· == w.2.2.2.2)) &&
    (match S.defOf w.2.2.1 with | some (.app g cs) => g == f && !cs.isEmpty | _ => false)

/-- Where an opening of `f` must start: a sequence's openings are told apart
by the number of arguments read before them. -/
def offOf (S : St P) (f : String) (tree : Bool) (n : Nat) : Option Nat :=
  if tree && S.prog.kind f == .assoc then some n else none

/-- The witness of `W` that reads argument `a` under `ctx` after `off`
arguments: one that names the node `a` itself when there is one; else the
first that names its class and does not name another of the arguments `later`
at this level, which is then the one it reads. Two arguments of one class are
told apart this way when the stream names each. -/
def Wit.pick (S : St P) (f : String) (tree : Bool) (ctx : Option Nat) (off : Option Nat) (a : Nat)
    (later : List Nat) (W : List Wit) : Option Wit :=
  (W.find? fun w => w.2.1 == a && Wit.reads S f tree ctx off a w).orElse fun _ =>
    W.find? fun w => !later.contains w.2.1 && Wit.reads S f tree ctx off a w

/-- The arguments `todo`, each with the opening it lies under, as one side of
a `:flatten` match reads them, after `out`: an argument a witness of `W` reads
(`Wit.reads`) is replaced by the arguments of the witness's member, which lie
under that witness and are read the same way with the witnesses left; each
witness is used once. Every other argument is one class, an application of
`f` included. -/
def viewArgs (S : St P) (f : String) (tree : Bool) (W : List Wit) (todo : List (Nat × Option Nat))
    (out : Array Nat := #[]) : List Nat :=
  match todo with
  | [] => out.toList
  | (a, ctx) :: rest =>
    match Wit.pick S f tree ctx (offOf S f tree out.size) a ((rest.filter (·.2 == ctx)).map (·.1)) W with
    | some w =>
      match S.defOf w.2.2.1 with
      | some (.app _ cs) =>
        if _h : (W.erase w).length < W.length then
          -- A multiset's argument has a count, and an opening reads all of its
          -- copies: every other copy of the node at this level goes with it.
          -- A regrouping stands for one occurrence of its class.
          let copies := if tree && S.prog.kind f == .ac then (rest.filter (· == (a, ctx))).length else 0
          let rest := if copies == 0 then rest else rest.filter (· != (a, ctx))
          let sub := cs.map (·, some w.1)
          viewArgs S f tree (W.erase w) ((List.replicate (copies + 1) sub).flatten ++ rest) out
        else viewArgs S f tree W rest (out.push a)
      | _ => viewArgs S f tree W rest (out.push a)
    | none => viewArgs S f tree W rest (out.push a)
termination_by (W.length, todo.length)

/-- The regrouping of `W` that reads the bound argument `b`: one that names
the node `b` itself when there is one; else the first that names its class and
does not name another of the arguments `others`, which is then the one it
reads. -/
def Wit.regroupOf (S : St P) (f : String) (W : List Wit) (b : Nat) (others : List Nat) : Option Wit :=
  match W.find? (fun w => w.2.1 == b && Wit.reads S f false none none b w) with
  | some w => some w
  | none => W.find? (fun w => Wit.reads S f false none none b w && !others.contains w.2.1)

/-- For a sequence operator, the positions in the bound arguments `bound` that
the regroupings `W` apply to, given the view `view` of the matched node: the
two are read left to right; a bound argument in the class of the view's next
element is that element, and one that is not, which a regrouping reads, is the
regrouping's member, whose arguments the view holds next. A stream's
regrouping does not say which occurrence of its class it is; this reading
fixes it without trying the others. -/
def regroupAt (S : St P) (f : String) (W : List Wit) (bound view : List Nat) (pos : Nat := 0)
    (out : List Nat := []) : List Nat :=
  match bound with
  | [] => out.reverse
  | b :: rest =>
    match view with
    | [] => out.reverse
    | v :: vs =>
      -- An argument a regrouping names, which is not the view's next node, is
      -- regrouped even when the two are in one class.
      let named := b != v && W.any fun w => w.2.1 == b && Wit.reads S f false none none b w
      if !named && S.fd b == S.fd v then regroupAt S f W rest vs (pos + 1) out
      else
        match Wit.regroupOf S f W b rest with
        | some w =>
          let n := match S.defOf w.2.2.1 with
            | some (.app _ cs) => cs.length
            | _ => 1
          regroupAt S f (W.erase w) rest (view.drop n) (pos + 1) (pos :: out)
        | none => regroupAt S f W rest vs (pos + 1) out

/-- The bound arguments with the one at each position of `at` replaced by the
arguments of the member of the regrouping that reads it, and an argument of
such a member that another regrouping reads replaced the same way: one pass
per regrouping, each over the arguments the pass before put in. -/
def viewAt (S : St P) (f : String) (W : List Wit) (at_ : List Nat) (bound : List Nat) : List Nat :=
  Id.run do
    let mut W := W
    let mut cur : Array (Nat × Bool) := (bound.zipIdx.map fun (b, i) => (b, at_.contains i)).toArray
    for _ in W do
      let mut out : Array (Nat × Bool) := #[]
      for ((b, fresh), i) in cur.toList.zipIdx do
        let later := ((cur.toList.drop (i + 1)).filter (·.2)).map (·.1)
        match (if fresh then Wit.regroupOf S f W b later else none) with
        | some w =>
          W := W.erase w
          match S.defOf w.2.2.1 with
          | some (.app _ cs) => out := out ++ (cs.map (·, true)).toArray
          | _ => out := out.push (b, false)
        | none => out := out.push (b, false)
      cur := out
    return (cur.map (·.1)).toList

/-- The arguments the regroupings `W` read that the bound arguments `bound`
do not hold, because the operator's laws dropped them from the match's view:
- a regrouping in the unit's class reads the unit, which the unit law adds;
- a regrouping in a class no bound argument is in, whose inverse the node's
  view `view` holds, reads a member of that class, which the inverse law adds
  together with that inverse;
- for an idempotent operator, a regrouping in a class the view holds an
  argument of reads one copy of the bound argument, and the view's argument is
  another. -/
def droppedRegroups (S : St P) (f : String) (W : List Wit) (bound view : List Nat) : List Nat :=
  let u := S.unit f
  let inv := (S.prog.opDecl? f).bind (·.inverse)
  -- Each regrouping stands for one occurrence of its class: a bound argument
  -- answers one regrouping, and `left` holds those not answered yet.
  (W.foldl (fun (acc : List Nat × List Nat) w =>
    let (out, left) := acc
    if (u.map S.fd) == some (S.fd w.2.1) then (out ++ u.toList, left)
    -- A set's argument the view holds as it is and a regrouping reads too:
    -- the argument twice is the argument once.
    else if S.prog.kind f == .aci && view.any (fun v => S.fd v == S.fd w.2.1) then
      (out ++ (bound.find? (fun b => S.fd b == S.fd w.2.1)).toList, left)
    else
      match left.find? (fun b => S.fd b == S.fd w.2.1) with
      | some b => (out, left.erase b)
      | none =>
        match inv with
        | some g =>
          match view.find? (fun e => match S.defOf e with
              | some (.app h [y]) => h == g && S.fd y == S.fd w.2.1
              | _ => false) with
          -- The class is named by a plain member: the kernel reads through an
          -- application of `f`.
          | some e => (out ++ [(S.plain.getD (S.fd w.2.1) none).getD w.2.1, e], left)
          | none => (out, left)
        | none => (out, left)) ([], bound)).1

/-- The fields of an `e` line after the operator: the nodes of the argument
patterns, and between `[` and `]` the nodes of each rest variable, in the
pattern's order. -/
def atomArgs (S : St P) (xs : List String) : Option (List (Nat × Nat) × List (List Nat)) := do
  let mut fixed : Array (Nat × Nat) := #[]
  let mut groups : Array (List Nat) := #[]
  let mut open? : Option (List String) := none
  for x in xs do
    match x, open? with
    | "[", none => open? := some []
    | "]", some g =>
      groups := groups.push (← ids S g.reverse)
      open? := none
    | "[", some _ => none
    | "]", none => none
    | _, some g => open? := some (x :: g)
    | _, none =>
      -- `c` or `c:k`: a node and the number of times the pattern takes it.
      match x.splitOn ":" with
      | [n] => fixed := fixed.push (← S.node? n, 1)
      | [n, k] =>
        let k ← k.toNat?
        if k == 0 then none
        fixed := fixed.push (← S.node? n, k)
      | _ => none
  if open?.isSome then none
  return (fixed.toList, groups.toList)

/-- The number of arguments the fields of an `e` line stand for. -/
def units (fixed : List (Nat × Nat)) : Nat := fixed.foldl (fun n e => n + e.2) 0

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

/-- The arguments node `x` is read as under a comb `f`, as the kernel's
`viewL` (`left`) or `viewR` reads them: through its first, or last, argument
when that is an application of `f`. -/
def kviewF (S : St P) (f : String) (left : Bool) (x : Nat) : List Nat :=
  match S.defOf x with
  | some (.app g cs) =>
    if g == f then
      match (if left then cs else cs.reverse) with
      | c :: rest =>
        if _h : c < x then
          if left then kviewF S f left c ++ rest else rest.reverse ++ kviewF S f left c
        else [x]
      | [] => [x]
    else [x]
  | _ => [x]
termination_by x

/-- A `cong` step for two nodes of a comb operator `f` (`:assoc-left`,
`:assoc-right`) whose arguments, read through the comb, are in one class
position by position. -/
def foldCong (S : St P) (f : String) (left : Bool) (a b : Nat) : St P × Pf := Id.run do
  if a == b then return (S, some none)
  -- The two nodes' own arguments, when they are in one class position by
  -- position (the kernel takes them as they are); else the arguments read
  -- through the comb.
  let own (x : Nat) : List Nat := match S.defOf x with
    | some (.app g cs) => if g == f then cs else [x]
    | _ => [x]
  let same (l m : List Nat) : Bool :=
    l.length == m.length && (l.zip m).all (fun (c, d) => S.fd c == S.fd d)
  let (l, m) := if same (own a) (own b) then (own a, own b)
    else (kviewF S f left a, kviewF S f left b)
  if !same l m then return (S, none)
  let mut S := S
  let mut prems : Array Nat := #[]
  for (c, d) in l.zip m do
    if c != d then
      let (S', p) := eqP S c d
      S := S'
      match p with
      | some (some s) => prems := prems.push s
      | _ => return (S, none)
  let (S', s) := emit S (.cong f a b prems.toList) a b
  return (S', some (some s))

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
  if kind.isFold then return foldCong S f (kind == .foldL) a b
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
  -- An argument of one node in the class of the other node: it goes to that
  -- node, which the kernel reads as its arguments.
  for (x, other) in [(a, b), (b, a)] do
    if !(argsOf other).isEmpty && (argsOf x).any (fun y => S.fd y == S.fd other)
        && !target.contains (S.fd other) then
      target := target.insert (S.fd other) other
  -- The kernel replaces an argument once and reads the result as it is: an
  -- argument that a replaced node flattens to stands for its own class.
  for (_, m) in target.toList do
    for z in kview S f m do
      if !target.contains (S.fd z) then target := target.insert (S.fd z) z
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
def inverseNode (S : St P) (inv : String) (a : Nat) (unit : Nat) (others : List Nat) :
    Option (Nat × Nat) :=
  let arg (m : Nat) : Option (Nat × Nat) :=
    match S.defOf m with
    | some (.app g [y]) => if g == inv then some (m, y) else none
    | _ => none
  let all := (arg a).toList ++ (S.inverses.filterMap fun m => if S.fd m == S.fd a then arg m else none)
    ++ (S.invIn.getD (S.fd a) []).filterMap arg
  -- The first that has what it cancels with, else the first.
  (all.find? fun (_, y) => S.fd y == S.fd unit || others.any fun b => S.fd b == S.fd y).orElse
    fun _ => all.head?

/-- `f` applied to `m`, a node the kernel accepts, or `none`. -/
def appNode (S : St P) (f : String) (m : List Nat) : St P × Option Nat :=
  let d := Node.app f m
  if m.isEmpty then (S, none)
  else match S.index[d]? with
    | some t => (S, some t)
    | none =>
      -- The table takes the node only if it is well-sorted.
      S.withCore fun c => c.addNode d

/-- One pass of `lawNormP` from `cur`, which `pf` proves equal to `x`: the
result when no inverse pair and no `n` arguments of one class are left, or
the next node, its proof, and the number of arguments it keeps. -/
def lawPass (S : St P) (f : String) (d : OpDecl) (u x cur : Nat) (pf : Pf) (peak : Bool) :
    St P × (Option (Nat × Pf) ⊕ (Nat × Pf × Nat)) := Id.run do
  let mut S := S
  -- In a critical pair's peak, an inverse pair is cancelled even when one of
  -- the two is in the unit's class: the unit's arguments stay.
  let atoms := (kview S f cur).filter fun a => peak || S.fd a != S.fd u
  -- What the next pass replaces by the unit: a node `f(..)` that a step
  -- proves is the unit, and the arguments it stands for.
  let mut found : Option (Nat × Nat × List Nat) := none
  if let some g := d.inverse then
    for a in atoms do
      if found.isNone then
        if let some (q, y) := inverseNode S g a u (atoms.erase a) then
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
  | none => return (S, .inl (some (cur, pf)))
  | some (pn, s1, rest) =>
    let (S1, t1) := appNode S f (pn :: rest)
    let (S1, t2) := appNode S1 f (u :: rest)
    S := S1
    let (some t1, some t2) := (t1, t2) | return (S, .inl none)
    let (S1, t3) := if rest.isEmpty then (S, some u) else appNode S f rest
    S := S1
    let some t3 := t3 | return (S, .inl none)
    let (S1, p1) := congStep S f cur t1
    let (S1, s2) := emit S1 (.cong f t1 t2 [s1]) t1 t2
    let (S1, p3) := congStep S1 f t2 t3
    let (S1, q) := transP S1 cur t2 p1 (some (some s2))
    let (S1, q) := transP S1 cur t3 q p3
    let (S1, q') := transP S1 x t3 pf q
    S := (S1.mergeBy cur t3 q)
    if q'.isNone then return (S, .inl none)
    return (S, .inr (t3, q', rest.length))

/-- The passes of `lawNormP`: each keeps fewer arguments than the one before,
and the recursion goes on only while that number decreases. -/
def lawNormGo (S : St P) (f : String) (d : OpDecl) (u x cur : Nat) (pf : Pf) (peak : Bool)
    (n : Nat) : St P × Option (Nat × Pf) :=
  match lawPass S f d u x cur pf peak with
  | (S, .inl r) => (S, r)
  | (S, .inr (cur', pf', k)) =>
    if _h : k < n then lawNormGo S f d u x cur' pf' peak k else (S, some (cur', pf'))
termination_by n

/-- Node `x` reduced by `f`'s inverse and nilpotent laws, and the proof that
`x` is the result. Each inverse pair `y, g(y)` becomes `f(f(y, g(y)), rest)`
by `f`'s laws, then `f(e, rest)` by the `inv` step, then `f(rest)`; each `n`
arguments of one class under `:nilpotent n` likewise, by the `nil` step. An
inverse of a node of the unit's class is first proved to be the unit. -/
def lawNormP (S : St P) (f : String) (x : Nat) (peak : Bool := false) :
    St P × Option (Nat × Pf) :=
  match S.prog.opDecl? f, S.unit f with
  | some d, some u =>
    if d.inverse.isNone && d.nilpotent.isNone then (S, some (x, some none))
    else lawNormGo S f d u x x (some none) peak ((kview S f x).length + 1)
  | _, _ => (S, some (x, some none))

/-- A step for `a = b` under `f`'s associativity, commutativity, idempotence
and unit, by the first of these that applies: `congStep`; all of one node's
arguments in the other's class; one node's arguments each standing for a
class, named by a plain member. -/
def congStepC (S : St P) (f : String) (a b : Nat) : St P × Pf :=
  -- Two nodes already in one class: the proof is read from the classes.
  if a != b && S.fd a == S.fd b then eqP S a b
  else
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
  else
  -- Both nodes with a plain member for each argument that is an application
  -- of `f`: each is its plain form argument by argument, and the plain forms
  -- are equal by `f`'s laws.
  let plainForm (S : St P) (x : Nat) : St P × Option Nat :=
    match S.defOf x with
    | some (.app g cs) =>
      if g != f || cs.isEmpty then (S, some x)
      else appNode S f (cs.map fun y =>
        match S.defOf y with
        | some (.app h _) => if h == f then (S.plain.getD (S.fd y) none).getD y else y
        | _ => y)
    | _ => (S, some x)
  let both (S : St P) : St P × Pf :=
    match plainForm S a with
    | (S, some pa) =>
      match plainForm S b with
      | (S, some pb) =>
        if pa == a && pb == b then (S, none)
        else
          let (S, p1) := congStep S f a pa
          -- The plain forms by `f`'s laws, or one of them an argument of
          -- the other's class.
          let (S, p2) := congStep S f pa pb
          let (S, p2) := if p2.isSome then (S, p2) else collapse S pa pb
          let (S, p2) := if p2.isSome then (S, p2) else
            (let (S, q) := collapse S pb pa
             if q.isSome then symmP S pb pa q else (S, none))
          let (S, p3) := congStep S f pb b
          let (S, q) := transP S a pb p1 p2
          transP S a b q p3
      | (S, none) => (S, none)
    | (S, none) => (S, none)
  let (S, p) := both S
  if p.isSome then (S, p)
  else
    -- `a`'s arguments, without the unit's, are the arguments of a node of the
    -- table in `b`'s class (or the same with `a`, `b` exchanged).
    let viaNode (S : St P) (x other : Nat) : St P × Pf :=
      match nodeOfArgs S f ((kview S f x).filter fun y => some (S.fd y) != u) with
      | some n =>
        if n != x && S.fd n == S.fd other then
          let (S, p1) := congStep S f x n
          if p1.isNone then (S, none)
          else
            let (S, p2) := eqP S n other
            transP S x other p1 p2
        else (S, none)
      | none => (S, none)
    let (S, p) := viaNode S a b
    if p.isSome then (S, p)
    else
      let (S, p) := viaNode S b a
      if p.isSome then (let (S, q) := symmP S b a p; (S, q))
      else
        -- The same with only the unit's node dropped from `a`'s arguments.
        match nodeOfArgs S f ((kview S f a).filter fun y => some y != S.unit f) with
        | some n =>
          if n != a && S.fd n == S.fd b then
            let (S, p1) := congStep S f a n
            if p1.isNone then (S, none)
            else
              let (S, p2) := eqP S n b
              transP S a b p1 p2
          else (S, none)
        | none => (S, none)

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

/-- A lattice merge of `x` and `y` under a cancellative operator `f`. The
stream gives node equations `n = f(children)` with counts, `pos` and `neg`,
such that, as sums over classes,
`x + sum pos (q * children n) + sum neg (q * n)` is
`y + sum pos (q * n) + sum neg (q * children n)`.
Each class is named by one member `R`, kept as one argument. The chain goes
from `f(x, z)` to `f(y, z)`, with `z = f(R of each equation)`, by steps of two
kinds: the two sides have the same arguments once nested applications are
read through (`cong` with no premise), or the same number of arguments, in
one class pairwise (`congStep`). In the middle, both sides hold the members
`R` of one multiset of classes. `cancel` then concludes. -/
def latticeP (S : St P) (x y : Nat) (pos neg : List (Nat × Nat)) : St P × Option (Option Nat) := Id.run do
  let some (n0, _) := (pos ++ neg).head? | return (S.fail "lattice: no equation", none)
  let some (.app f _) := S.defOf n0 | return (S.fail "lattice: equation of no application", none)
  let rep (c : Nat) : Nat := (S.plain.getD (S.fd c) none).getD (S.fd c)
  let kids (n : Nat) : List Nat := match S.defOf n with
    | some (.app _ cs) => cs
    | _ => []
  let each (g : Nat → List Nat) (ps : List (Nat × Nat)) : List Nat :=
    ps.flatMap fun (n, q) => (List.replicate q (g n)).flatten
  let one (g : Nat → Nat) : Nat → List Nat := fun n => [g n]
  let rx := rep x
  let ry := rep y
  let zs := each (one rep) pos ++ each (one rep) neg
  -- The sums, from `f(x, z)` to `f(y, z)`; `true` marks a link whose two
  -- sides have the same arguments read through.
  let sums : List (List Nat × Bool) := [
    ([rx] ++ zs, true),
    ([rx] ++ each (one id) pos ++ each (one rep) neg, false),
    ([rx] ++ each kids pos ++ each (one rep) neg, true),
    ([rx] ++ each (fun n => (kids n).map rep) pos ++ each (one rep) neg, false),
    ([ry] ++ each (one rep) pos ++ each (fun n => (kids n).map rep) neg, true),
    ([ry] ++ each (one rep) pos ++ each kids neg, false),
    ([ry] ++ each (one rep) pos ++ each (one id) neg, true),
    ([ry] ++ zs, false)]
  let mut S := S
  let (S1, z) := appNode S f zs
  let some z := z | return (S1.fail "lattice: sum ill-sorted", none)
  let (S1, a4) := appNode S1 f [rx, z]
  let (S1, b4) := appNode S1 f [ry, z]
  S := S1
  let (some a4, some b4) := (a4, b4) | return (S.fail "lattice: sum ill-sorted", none)
  let mut cur := a4
  let mut pf : Pf := some none
  for (args, flat) in sums ++ [([ry, z], true)] do
    let (S1, i) := if args == [ry, z] then (S, some b4) else appNode S f args
    let some i := i | return (S1.fail "lattice: sum ill-sorted", none)
    S := S1
    if i != cur then
      let (S1, p) : St P × Pf :=
        if flat then
          let (S1, s) := emit S (.cong f cur i []) cur i
          (S1, some (some s))
        else congStep S f cur i
      if p.isNone then return (S1.fail s!"lattice: sums differ | {cur} = {repr (S1.defOf cur)}, {i} = {repr (S1.defOf i)}", none)
      let (S1, q) := transP S1 a4 i pf p
      S := S1
      pf := q
      cur := i
  match stepOf S a4 pf with
  | (S1, some st) =>
    let (S1, c) := emit S1 (.cancel f st rx ry z) rx ry
    let S1 := S1.mergeBy rx ry (some (some c))
    let (S1, q) := eqP S1 x y
    return (S1, q)
  | (S1, none) => return (S1, none)

/-- `n = other` for a node `n` of the sequence operator `f` whose arguments,
read through nested applications, hold those of `l` as a run: `n` is
`f(before, l, after)` read through, which is `f(before, r, after)` argument by
argument since `l = r` is one class, which is `other` under `f`'s laws. The
run is the first one, as the engine takes it. -/
def seqReduce (S : St P) (f : String) (n other l r : Nat) : St P × Option (Option Nat) := Id.run do
  -- A comb: the rule's left side is the node's first (or last) argument read
  -- through, so the node is `f(l, rest)` (or `f(rest, l)`).
  if (S.prog.kind f).isFold then
    let left := S.prog.kind f == .foldL
    let (vn, vl) := (kviewF S f left n, kviewF S f left l)
    if S.fd l != S.fd r || vl.length > vn.length then return (S, none)
    let rest := if left then vn.drop vl.length else vn.take (vn.length - vl.length)
    let (S, x1) := appNode S f (if left then l :: rest else rest ++ [l])
    let (S, x2) := appNode S f (if left then r :: rest else rest ++ [r])
    let (some x1, some x2) := (x1, x2) | return (S, none)
    let (S, p1) := foldCong S f left n x1
    -- `f(l, rest) = f(r, rest)` argument by argument, from `l = r`.
    let (S, lr) := eqP S l r
    let (S, lrStep) := stepOf S l lr
    let (S, p2) : St P × Pf := if x1 == x2 then (S, some none) else
      match lrStep with
      | some e => let (S, t) := emit S (.cong f x1 x2 (if l == r then [] else [e])) x1 x2; (S, some (some t))
      | none => (S, none)
    let (S, p3) := foldCong S f left x2 other
    if p1.isNone || p2.isNone || p3.isNone then return (S, none)
    let (S, p) := transP S n x2 p1 p2
    let (S, p) := transP S n other p p3
    return (S, p)
  let args := kview S f n
  let ls := kview S f l
  if ls.isEmpty || S.fd l != S.fd r then return (S, none)
  let at_ := (List.range (args.length + 1 - ls.length)).find? fun i =>
    ((args.drop i).take ls.length).map S.fd == ls.map S.fd
  let some i := at_ | return (S, none)
  let pre := args.take i
  let suf := args.drop (i + ls.length)
  let (S, x1) := appNode S f (pre ++ [l] ++ suf)
  let (S, x2) := appNode S f (pre ++ [r] ++ suf)
  let (some x1, some x2) := (x1, x2) | return (S, none)
  let (S, p1) := congStepL S f n x1
  let (S, p2) := congStep S f x1 x2
  let (S, p3) := congStepL S f x2 other
  if p1.isNone || p2.isNone || p3.isNone then return (S, none)
  let (S, p) := transP S n x2 p1 p2
  let (S, p) := transP S n other p p3
  return (S, p)

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
  | some (.napp f _) => (S.prog.opDecl? f).map (·.res)
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
        | .napp _ _ => false
      let S := match d with
        | .app g [_] => if S.invOps.contains g then { S with invIn := S.invIn.insert t [t] } else S
        | _ => S
      ({ S with plain := (if S.plain.size ≤ t then S.plain ++ Array.replicate (t + 1 - S.plain.size) none
                else S.plain).setIfInBounds t (if isPlain then some t else none) }, some t)
    | (S, none) => (S, none)

/-- `writtenP` for an application whose arguments' terms are `ws`. -/
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

/-- A program term as the kernel interns it, the node it evaluated to, and
the proof that the two are equal: each argument's term is its node, and `f` of
the argument terms is the node by `f`'s laws (a nested application of an
associative operator, which the engine's term builder splices, among them).
The terms join their nodes' classes. -/
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

/-- `low = y`, for `low = f(unit, rest)`: under `f`'s laws; or, when `rest` is
one argument, `low` is that argument by the unit law, which is in `y`'s
class. -/
def lowTo (S : St P) (f : String) (low : Nat) (rest : List Nat) (y : Nat) : St P × Pf :=
  let (S, p) := congStepL S f low y
  if p.isSome then (S, p)
  else
    match rest with
    | [r0] =>
      let (S, p1) := congStepL S f low r0
      let (S, p2) := eqP S r0 y
      if p1.isNone || p2.isNone then (S, none) else transP S low y p1 p2
    | _ => (S, none)

/-- `x = y` when node `x`, an application of `f`, holds `g(c)` and what `c` is
read as (`c` itself, or the arguments of `c` when it is an application of
`f`): `x` is `f(f(c, g(c)), rest)` read through, `f(c, g(c))` is the unit by
the `inv` step, and `f(unit, rest)` is `y` by the unit law. -/
def invDirect (S : St P) (f : String) (x y : Nat) : St P × Pf := Id.run do
  let (some (.app _ _), some u) := (S.defOf x, S.unit f) | return (S, none)
  let args := kview S f x
  let g := (S.prog.opDecl? f).bind (·.inverse)
  if !(S.prog.kind f == .ac || S.prog.kind f == .aci) then return (S, none)
  for q in args do
    let some (.app h [c]) := S.defOf q | continue
    if some h != g then continue
    let take (cs : List Nat) : Option (List Nat) :=
      cs.foldl (fun (r : Option (List Nat)) k =>
        r.bind fun r => if r.contains k then some (r.erase k) else none) (some (args.erase q))
    let open_ := match S.defOf c with
      | some (.app h' _) => if h' == f then take (kview S f c) else none
      | _ => none
    let some rest := (take [c]).orElse fun _ => open_ | continue
    let (S, pn) := appNode S f [c, q]
    let some pn := pn | return (S, none)
    let (S, s) := emit S (.inv f pn c q u) pn u
    if rest.isEmpty then
      -- `x` is `f(c, g(c))` read through.
      let (S, p1) : St P × Pf := if pn == x then (S, some none) else
        (let (S, t) := emit S (.cong f x pn []) x pn; (S, some (some t)))
      let (S, p) := transP S x u p1 (some (some s))
      let (S, p3) := eqP S u y
      if p3.isNone then return (S, none)
      return transP S x y p p3
    let (S, mid) := appNode S f (pn :: rest)
    let (S, low) := appNode S f (u :: rest)
    let (some mid, some low) := (mid, low) | return (S, none)
    let (S, p1) : St P × Pf := if mid == x then (S, some none) else
      (let (S, t) := emit S (.cong f x mid []) x mid; (S, some (some t)))
    let (S, t2) := emit S (.cong f mid low [s]) mid low
    let (S, p3) := lowTo S f low rest y
    if p3.isNone then return (S, none)
    let (S, p) := transP S x low p1 (some (some t2))
    return transP S x y p p3
  -- The same on classes: an argument that is an application of `f` stands for
  -- its class, named by a plain member; an argument in the class of an
  -- inverse application `g(c)`, with another argument in `c`'s class, cancels.
  let (S, xp) := plainArgs S f x
  let some xp := xp | return (S, none)
  let cls : List Nat := match S.defOf xp with
    | some (.app _ cs) => cs
    | _ => []
  for a in cls do
    for q in (S.invIn.getD (S.fd a) []) do
      let some (.app h [c]) := S.defOf q | continue
      if some h != g then continue
      let some b := (cls.erase a).find? (fun b => S.fd b == S.fd c) | continue
      let rest : List Nat := (cls.erase a).erase b
      let (S, pn) := appNode S f [c, q]
      let some pn := pn | return (S, none)
      let (S, s) := emit S (.inv f pn c q u) pn u
      let (S, p0) : St P × Pf := if xp == x then (S, some none) else congStep S f x xp
      let (S, mid, low, pml) : St P × Nat × Nat × Pf :=
        if rest.isEmpty then (S, pn, u, some (some s))
        else
          match appNode S f (pn :: rest) with
          | (S, some mid) =>
            match appNode S f (u :: rest) with
            | (S, some low) =>
              let (S, t2) := emit S (.cong f mid low [s]) mid low
              (S, mid, low, some (some t2))
            | (S, none) => (S, mid, mid, none)
          | (S, none) => (S, pn, pn, none)
      let (S, p1) := congStepL S f xp mid
      let (S, p3) := lowTo S f low rest y
      if p0.isNone || p1.isNone || pml.isNone || p3.isNone then return (S, none)
      let (S, p) := transP S x mid p0 p1
      let (S, p) := transP S x low p pml
      return transP S x y p p3
  return (S, none)

/-- The merge of `a` and `b` by `invDirect`, from either node: for a
completion merge whose derivation gives no kernel step. -/
def invTry (S : St P) (a b : Nat) : St P :=
  let try_ (S : St P) (x y : Nat) : St P × Pf :=
    match S.defOf x with
    | some (.app f _) => invDirect S f x y
    | _ => (S, none)
  let (S, p) := try_ S a b
  let (S, p) := if p.isSome then (S, p) else (let (S, q) := try_ S b a; symmP S b a q)
  S.mergeBy a b p

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
    -- A hop with no step is not a merge: the chain then has no proof.
    let S := if p.isSome then S.mergeBy cur next p else S
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
        S := if pl.isSome then S'.mergeBy l' st.l pl else S'
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
    S := if p2.isSome then S.mergeBy t1 t2 p2 else S
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
          S := if pr.isSome then S'.mergeBy r r' pr else S'
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
  -- A target node whose arguments are applications of `f`, each standing for
  -- its class: the hop goes to its copy with plain arguments, which is the
  -- target argument by argument.
  if let .inl _ := c.target then
    let (S', t') := plainArgs S f target
    S := S'
    if let some t' := t' then
      if t' != target then
        let (S', pt) := congStep S f t' target
        S := if pt.isSome then S'.mergeBy t' target pt else S'
        let (S', pf') := hop S cur t' pf
        S := S'; pf := pf'; cur := t'
  let (S', pf') := hop S cur target pf
  return (S', some (start, target, pf'))

/-- The kernel steps of a `t` line, whose check passed: the term as the
program writes it (its arguments' own terms as arguments) is node `i`. -/
def termLine (S : St P) (i : Nat) (f : String) (cs : List Nat) : St P := Id.run do
  let done (S : St P) : St P := { S with splices := [], opens := [], regroups := [], inverses := [] }
  -- The application to no argument is the unit, by the `unit` step.
  let S := match cs, S.unit f with
    | [], some u =>
      match intern S (Node.app f []) with
      | (S, some w) =>
        if S.fd w == S.fd u then S
        else let (S, st) := emit S (.unit f w u) w u; S.mergeBy w u (some (some st))
      | (S, none) => S
    | _, _ => S
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
  /-- The nodes each rest variable is bound to. -/
  ρ : List (String × List Nat) := []
  /-- The count each multiplicity variable is bound to. -/
  μ : List (String × Nat) := []
  /-- The position of the next `e` line. -/
  atomIdx : Nat := 0
  atoms : List (Nat × String × List (Nat × Nat) × List (List Nat))
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
  | .rest _ => none
  | .rep _ _ => none
  | .times _ _ => none
  | .count _ => none
  | .lit s v => some (.lit s v)
  | .app f ps => (Pat.toTerms? ps).map (.app f)

def Pat.toTerms? : List Pat → Option (List Term)
  | [] => some []
  | p :: ps => (Pat.toTerm? p).bind fun t => (Pat.toTerms? ps).map (t :: ·)

end

/-- The number of arguments the patterns that are no rest variable take, when
none is a repeated argument (whose count the pattern does not give). -/
def fixedArgs (ps : List Pat) : Option Nat :=
  if ps.any (fun p => match p with | .rep _ _ => true | _ => false) then none
  else some (ps.foldl (fun n p => match p with
    | .rest _ => n
    | .times _ k => n + k
    | _ => n + 1) 0)

mutual

/-- The operator and the number of arguments of the first line a pattern's
match writes: that of its first innermost application or literal. -/
def firstLine : Pat → String × Option Nat
  | .var _ => ("", some 0)
  | .rest _ => ("", some 0)
  | .rep _ _ => ("", some 0)
  | .times _ _ => ("", some 0)
  | .count _ => ("", some 0)
  | .lit _ _ => ("#lit", some 0)
  | .app f ps => (firstOf ps).getD (f, fixedArgs ps)

/-- The first line of the first pattern that is no variable. -/
def firstOf : List Pat → Option (String × Option Nat)
  | [] => none
  | .var _ :: ps => firstOf ps
  | .rest _ :: ps => firstOf ps
  | .rep (.var _) _ :: ps => firstOf ps
  | .rep (.lit s v) _ :: _ => some (firstLine (.lit s v))
  | .rep (.app f qs) _ :: _ => some (firstLine (.app f qs))
  | .rep (.rest _) _ :: ps => firstOf ps
  | .rep (.rep _ _) _ :: ps => firstOf ps
  | .rep (.times _ _) _ :: ps => firstOf ps
  | .rep (.count _) _ :: ps => firstOf ps
  | .times (.var _) _ :: ps => firstOf ps
  | .times (.lit s v) _ :: _ => some (firstLine (.lit s v))
  | .times (.app f qs) _ :: _ => some (firstLine (.app f qs))
  | .times (.rest _) _ :: ps => firstOf ps
  | .times (.rep _ _) _ :: ps => firstOf ps
  | .times (.times _ _) _ :: ps => firstOf ps
  | .times (.count _) _ :: ps => firstOf ps
  | .count _ :: ps => firstOf ps
  | .lit s v :: _ => some (firstLine (.lit s v))
  | .app f qs :: _ => some (firstLine (.app f qs))

end

/-- The regroupings of `W` that name a later argument of `rest` at this level
(at a position of `only`, when given): each is that argument's, so the
arguments of an earlier argument's member do not take it. -/
def keptWits (tree : Bool) (only : Option (List Nat)) (at_ : Nat) (rest : List Nat) (W : List Wit) :
    List Wit :=
  if tree then [] else
    (rest.zipIdx.foldl (fun (acc : List Wit × List Wit) (r, j) =>
      let mine := match only with
        | some ps => ps.contains (at_ + 1 + j)
        | none => true
      match (if mine then acc.2.find? (fun v => v.2.1 == r) else none) with
      | some v => (v :: acc.1, acc.2.erase v)
      | none => acc) ([], W)).1

def innerWits (kept W : List Wit) : List Wit := W.filter fun v => !kept.contains v

mutual

/-- Node `x`, which lies under the opening `ctx` and starts after `off`
arguments read, as the kernel must read it for one side of a `:flatten`
match: an argument a witness of `W` reads becomes the witness's member, read
the same way with the witnesses left, whose arguments the kernel reads in its
place; an argument that is an application of `f` with no witness becomes a
plain member of its class, which the kernel reads as one argument. The result,
the proof that `x` is it (argument by argument), the witnesses left, and the
number of arguments `x` is read as. -/
def openNode (S : St P) (f : String) (tree : Bool) (ctx : Option Nat) (x : Nat) (W : List Wit)
    (only : Option (List Nat) := none) (off : Nat := 0) :
    St P × Option (Nat × Pf) × List Wit × Nat :=
  match S.defOf x with
  | some (.app g args) =>
    if g != f then (S, some (x, some none), W, 1)
    else
      match openArgs S f tree ctx W args #[] #[] false [] only off with
      | (S, some (out, prems, changed), W', n) =>
        if !changed then (S, some (x, some none), W', n)
        else
          match appNode S f out.toList with
          | (S, some x') =>
            if x' == x then (S, some (x, some none), W', n)
            else
              let (S, st) := emit S (.cong f x x' prems.toList) x x'
              (S, some (x', some (some st)), W', n)
          | (S, none) => (S, none, W', n)
      | (S, none, W', n) => (S, none, W', n)
  | _ => (S, some (x, some none), W, 1)
termination_by (W.length, 1, 0)

/-- The arguments of `openNode`'s result, after `out`, and a step for each
argument replaced, after `prems`; `off` counts the arguments read so far. -/
def openArgs (S : St P) (f : String) (tree : Bool) (ctx : Option Nat) (W : List Wit)
    (args : List Nat) (out : Array Nat) (prems : Array Nat) (changed : Bool)
    (opened : List (Nat × Nat) := []) (only : Option (List Nat) := none) (off : Nat := 0) :
    St P × Option (Array Nat × Array Nat × Bool) × List Wit × Nat :=
  match args with
  | [] => (S, some (out, prems, changed), W, off)
  | a :: rest =>
    let isApp (m : Nat) : Bool :=
      match S.defOf m with
      | some (.app h cs) => h == f && !cs.isEmpty
      | _ => false
    -- A multiset's argument an opening already read: its other copies become
    -- the same node.
    let again := if tree && S.prog.kind f == .ac then opened.lookup a else none
    -- With `only`, a witness applies at the listed positions and nowhere else.
    let here := match only with
      | some ps => ps.contains out.size
      | none => true
    -- The node the argument becomes, the witnesses left, and the arguments read.
    let r : St P × Option Nat × List Wit × Nat :=
      if let some to := again then (S, some to, W, off + 1) else
      match (if here then Wit.pick S f tree ctx (offOf S f tree off) a rest W else none) with
      | some w =>
        if _h : (innerWits (keptWits tree only out.size rest (W.erase w)) (W.erase w)).length < W.length then
          let kept := keptWits tree only out.size rest (W.erase w)
          match openNode S f tree (some w.1) w.2.2.1
              (innerWits (keptWits tree only out.size rest (W.erase w)) (W.erase w)) none off with
          | (S, some (m', pm), W', n) =>
            -- `a` is the member, which is its opened form.
            let (S, p) := eqP S a w.2.2.1
            let (S, q) := transP S a m' p pm
            let S := S.mergeBy a m' q
            let W' := W' ++ kept.reverse
            if W'.length ≤ (W.erase w).length then (S, some m', W', n) else (S, none, W, off)
          | (S, none, _, _) => (S, none, W, off)
        else (S, none, W, off)
      | none => (S, some (if isApp a then (S.plain.getD (S.fd a) none).getD a else a), W, off + 1)
    match r with
    | (S, none, _, _) => (S, none, W, off)
    | (S, some to, W', off') =>
      if _h : W'.length ≤ W.length then
        if to != a then
          let (S, p) := eqP S a to
          match stepOf S a p with
          | (S, some st) =>
            openArgs S f tree ctx W' rest (out.push to) (prems.push st) true ((a, to) :: opened) only
              off'
          | (S, none) => (S, none, W', off')
        else openArgs S f tree ctx W' rest (out.push to) prems changed opened only off'
      else (S, none, W, off)
termination_by (W.length, 0, args.length)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and, Nat.lt_succ_self, and_true]
  all_goals omega

end

/-- The instance `i` of a comb pattern is the matched node `n`, whose view
read the openings `W` (root first): each opened class is in the comb position
(first argument of a left comb, last of a right one) of the node before it,
and stands for its member. From the last opening back, each node gets the next
one's node in that position, argument by argument; the root so rebuilt reads
as the instance position by position, the instance's comb-position argument
standing for a regrouping's member when `R` has one for its class. -/
def foldInst (S : St P) (f : String) (left : Bool) (i n : Nat) (W : List Wit)
    (R : List Wit := []) : St P × Pf := Id.run do
  -- `x` with its comb-position argument replaced by `y`, and the proof that
  -- the two are equal, given `y`'s proof from the member `m` it stands for.
  let put (S : St P) (x m y : Nat) (pm : Pf) : St P × Option (Nat × Pf) :=
    match S.defOf x with
    | some (.app _ cs) =>
      let arg := if left then cs.head? else cs.getLast?
      match arg with
      | some a =>
        let cs' := if left then y :: cs.drop 1 else cs.dropLast ++ [y]
        match appNode S f cs' with
        | (S, some x') =>
          if x' == x then (S, some (x, some none))
          else
            -- `a` is in `m`'s class, and `m` is `y`.
            let (S, p1) := eqP S a m
            let (S, p) := transP S a y p1 pm
            match stepOf S a p with
            | (S, some st) =>
              let (S, t) := emit S (.cong f x x' (if a == y then [] else [st])) x x'
              (S, some (x', some (some t)))
            | (S, none) => (S, none)
        | (S, none) => (S, none)
      | none => (S, none)
    | _ => (S, none)
  -- `x` with a plain member of its class in place of its comb-position
  -- argument, when that argument is an application of `f` that no opening
  -- reads through: the kernel would read through it.
  let norm (S : St P) (x : Nat) : St P × Nat × Pf :=
    match S.defOf x with
    | some (.app _ cs) =>
      match (if left then cs.head? else cs.getLast?) with
      | some a =>
        let isApp := match S.defOf a with
          | some (.app g as) => g == f && !as.isEmpty
          | _ => false
        match isApp, S.plain.getD (S.fd a) none with
        | true, some pm =>
          let (S, pe) := eqP S a pm
          match put S x a pm pe with
          | (S, some (x', p)) => (S, x', p)
          | (S, none) => (S, x, some none)
        | _, _ => (S, x, some none)
      | none => (S, x, some none)
    | _ => (S, x, some none)
  let mut S := S
  -- The node the current opening's member is read as, and the proof.
  let mut acc : Option (Nat × Nat × Pf) := none
  for w in W.reverse do
    let m := w.2.2.1
    match acc with
    | none =>
      -- The innermost member's own comb-position argument is an element.
      let (S1, m', pm') := norm S m
      S := S1
      acc := some (m, m', pm')
    | some (cm, cy, cp) =>
      match put S m cm cy cp with
      | (S1, some (m', pm')) => S := S1; acc := some (m, m', pm')
      | (S1, none) => return (S1, none)
  let (S1, root, pr) ← match acc with
    | none => pure (norm S n)
    | some (cm, cy, cp) =>
      match put S n cm cy cp with
      | (S1, some (n', pn')) => pure (S1, n', pn')
      | (S1, none) => return (S1, none)
  -- The instance's argument in the comb position is one element of the
  -- pattern: when it is an application of `f`, which the kernel would read
  -- through, a plain member of its class takes its place.
  let (S1, i', pi) : St P × Nat × Pf :=
    match S1.defOf i with
    | some (.app _ cs) =>
      match (if left then cs.head? else cs.getLast?) with
      | some a =>
        let isApp := match S1.defOf a with
          | some (.app g as) => g == f && !as.isEmpty
          | _ => false
        -- A regrouping of the argument's class: the argument stands for the
        -- member's arguments, which the comb reads in its place.
        match R.find? (fun w => S1.fd w.2.1 == S1.fd a) with
        | some w =>
          let m := w.2.2.1
          let (S2, pe) := eqP S1 a m
          match put S2 i a m pe with
          | (S2, some (i', p)) => (S2, i', p)
          | (S2, none) => (S2, i, some none)
        | none =>
        match isApp, S1.plain.getD (S1.fd a) none with
        | true, some pm =>
          let (S2, pe) := eqP S1 a pm
          match put S2 i a pm pe with
          | (S2, some (i', p)) => (S2, i', p)
          | (S2, none) => (S2, i, some none)
        | _, _ => (S1, i, some none)
      | none => (S1, i, some none)
    | _ => (S1, i, some none)
  let (S1, p2) := foldCong S1 f left i' root
  if pr.isNone || p2.isNone || pi.isNone then return (S1, none)
  let (S1, p2) := transP S1 i root pi p2
  let (S1, pr') := symmP S1 n root pr
  transP S1 i n p2 pr'

/-- The proof that the instance `i` of an application pattern is the node `n`
it matched on the `e` line at position `k`: by `f`'s laws and, for a
`:flatten` match, with each side first read under its witnesses (`openNode`). -/
def instProof (S : St P) (f : String) (i n : Nat) (k : Option Nat) : St P × Pf :=
  let (wo, wr) := match k with
    | some k => witsOf S k
    | none => ([], [])
  if (S.prog.kind f).isFold then foldInst S f (S.prog.kind f == .foldL) i n wo wr
  else if wo.isEmpty && wr.isEmpty then congStepL S f i n
  else
    let argsOf (S : St P) (x : Nat) : List Nat := match S.defOf x with
      | some (.app _ cs) => cs
      | _ => []
    -- A regrouping whose class the laws dropped reads an argument the instance
    -- gets back (`droppedRegroups`): the two are equal by the unit or inverse
    -- law.
    let extra := droppedRegroups S f wr (argsOf S i)
      (viewArgs S f true wo ((argsOf S n).map (·, none)))
    let (S, i0, p0) : St P × Nat × Pf :=
      if extra.isEmpty then (S, i, some none)
      else match appNode S f (argsOf S i ++ extra) with
        | (S, some i0) => let (S, p) := congStepL S f i i0; (S, i0, p)
        | (S, none) => (S, i, none)
    -- A sequence's regroupings apply where the node's view puts them.
    let only := if S.prog.kind f == .assoc && !wr.isEmpty then
        some (regroupAt S f wr (argsOf S i0) (viewArgs S f true wo ((argsOf S n).map (·, none))))
      else none
    match openNode S f true none n wo with
    | (S, some (n', pn), _, _) =>
      match openNode S f false none i0 wr only with
      | (S, some (i', pi), _, _) =>
        let (S, p) := congStepL S f i' n'
        let (S, q) := transP S i i0 (some none) p0
        let (S, q) := transP S i i' q pi
        let (S, q) := transP S i n' q p
        let (S, pn') := symmP S n n' pn
        transP S i n q pn'
      | (S, none, _, _) => (S, none)
    | (S, none, _, _) => (S, none)

/-- The instance `f(ic)` of an application pattern, joined to node `n`. -/
def instOf (f : String) (ic : List Nat) (n : Nat) (k : Option Nat := none) : WalkM P Nat := do
  let d := Node.app f ic
  let i ← withS fun S => intern S d
  match i with
  | some i =>
    withS fun S =>
      -- The application to no argument is the unit, by the `unit` step.
      let S := match ic, S.unit f with
        | [], some u =>
          if S.fd i == S.fd u then S
          else let (S, st) := emit S (.unit f i u) i u; S.mergeBy i u (some (some st))
        | _, _ => S
      let (S, p) := instProof S f i n k
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
  | .app f ps, (_, h, cs, _) :: _ =>
    let (g, k) := firstLine q
    -- The line is for `q`'s first inner application, or for `q` itself when
    -- its ground arguments are `let` names, which have no line.
    if (g == h && k.all (· == units cs)) || (f == h && (fixedArgs ps).all (· == units cs)) then pure none
    else pure ((Pat.toTerm? q).bind (eval w.S))
  | .app _ _, [] => pure ((Pat.toTerm? q).bind (eval w.S))
  | _, _ => pure none

/-- The application pattern `f(ps)` against the next line, once each argument
that is no variable has its matched node and instance in `sub`. -/
def walkApp (key : String) (f : String) (ps : List Pat) (sub : List (Option (Nat × Nat))) :
    WalkM P (Nat × Nat) := do
  let w ← get
  match w.atoms with
  | (n, g, fixed, groups) :: rest =>
    let S := w.S
    if g != f || !(fixedArgs ps).all (· == units fixed) then
      throw "rule: line for another application"
    -- A count above the kernel's limit: each argument takes its field whole,
    -- and the instance is the counted node itself.
    if fixed.any (fun e => e.2 > Ctx.countLimit) then
      if !groups.isEmpty then throw "rule: a rest variable beside a count above the limit"
      let mut σ := w.σ
      let mut μ := w.μ
      let mut cks : Array (Nat × Nat) := #[]
      let mut fixed := fixed
      for (q, o) in ps.zip sub do
        let (c, cnt) :: restF := fixed | throw "rule: argument differs | no field left"
        fixed := restF
        let q ← match q with
          | .rep q k =>
            match μ.lookup k with
            | some v => if v != cnt then throw "rule: multiplicity variable bound twice"
            | none => μ := (k, cnt) :: μ
            pure q
          | .times q k =>
            if k != cnt then throw "rule: argument differs | another count"
            pure q
          | q =>
            if cnt != 1 then throw "rule: argument differs | another count"
            pure q
        let inst ← match q, o with
          | .var x, _ =>
            match σ.lookup x with
            | some y =>
              if S.fd y != S.fd c then throw "rule: variable bound twice"
              pure y
            | none =>
              σ := (x, c) :: σ
              pure c
          | _, some (m, i) =>
            if S.fd m != S.fd c then throw "rule: argument differs | the argument's match is not in the field's class"
            pure i
          | _, none => throw "rule: argument differs | an argument pattern with no match"
        cks := cks.push (inst, cnt)
      if !fixed.isEmpty then throw "rule: line for another application"
      set { w with atoms := rest, atomIdx := w.atomIdx + 1, σ := σ, μ := μ }
      match ← withS fun S => intern S (countedNode f cks.toList) with
      | some i =>
        if i != n then throw "rule: counted node differs"
        modify fun w => { w with memo := (key, n, i) :: w.memo }
        return (n, i)
      | none => throw "rule: instance ill-sorted"
    let mut σ := w.σ
    let mut ρ := w.ρ
    let mut μ := w.μ
    let mut ic : Array Nat := #[]
    -- The nodes the line binds, in the pattern's order: an argument's node
    -- (as many times as a repeated argument's count), or a rest variable's
    -- nodes.
    let mut bound : Array Nat := #[]
    let mut fixed := fixed
    let mut groups := groups
    for (q, o) in ps.zip sub do
      -- A rest variable takes the next group of nodes.
      if let .rest x := q then
        let grp := groups.headD []
        groups := groups.tail
        bound := bound ++ grp.toArray
        match ρ.lookup x with
        | some ys =>
          if ys.length != grp.length || (ys.zip grp).any (fun (y, c) => S.fd y != S.fd c) then
            throw "rule: rest variable bound twice"
          ic := ic ++ ys.toArray
        | none =>
          ρ := (x, grp) :: ρ
          ic := ic ++ grp.toArray
        continue
      -- A repeated argument takes the next field whole, and its count; any
      -- other argument takes one of the field's copies.
      let (q, times) ← match q, fixed with
        | .rep q k, (_, cnt) :: _ =>
          match μ.lookup k with
          | some v => if v != cnt then throw "rule: multiplicity variable bound twice"
          | none => μ := (k, cnt) :: μ
          pure (q, cnt)
        | .rep _ _, [] => throw "rule: argument differs | no field for a repeated argument"
        | .times q k, _ => pure (q, k)
        | q, _ => pure (q, 1)
      let c ← match fixed with
        | (c, cnt) :: rest =>
          if cnt < times then throw "rule: argument differs | a field with fewer copies than the argument's count"
          fixed := if cnt == times then rest else (c, cnt - times) :: rest
          pure c
        | [] => throw "rule: argument differs | no field left"
      let inst ← match q, o with
        | .var x, _ =>
          match σ.lookup x with
          | some y =>
            if S.fd y != S.fd c then throw "rule: variable bound twice"
            pure y
          | none =>
            σ := (x, c) :: σ
            pure c
        | _, some (m, i) =>
          if S.fd m != S.fd c then throw s!"rule: argument differs | the argument's match {m} is not in the field's class {c}"
          pure i
        | _, none => throw "rule: argument differs | an argument pattern with no match"
      for _ in [0:times] do
        bound := bound.push c
        ic := ic.push inst
    if !fixed.isEmpty || !groups.isEmpty then throw "rule: line for another application"
    let cs := bound.toList
    match S.defOf n with
    | some (.app h ds) =>
      -- The node's arguments under the openings (`s` lines), the bound nodes
      -- under the regroupings (`y` lines), then both as classes.
      let S0 := { S with splices := [] }
      let (wo, wr) := witsOf S w.atomIdx
      let vd := viewArgs S f true wo (ds.map (·, none))
      let csU := cs ++ droppedRegroups S f wr cs vd
      let vc := if S.prog.kind f == .assoc && !wr.isEmpty then
          viewAt S f wr (regroupAt S f wr csU vd) csU
        else viewArgs S f false wr (csU.map (·, none))
      if h != f || (let (x, y) := nf2 S0 f vd vc; x != y) then
        throw s!"rule: matched node differs | node {n} of {h} with arguments {ds} read as {vd}, classes {(nf2 S0 f vd vc).1}; pattern bound to {cs} read as {vc}, classes {(nf2 S0 f vd vc).2}; openings {wo.map fun w => (w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2)}, regroupings {wr.map fun w => (w.2.1, w.2.2.1)}, placed {regroupAt S f wr csU vd}, fd {csU.map S.fd} {wr.map fun w => S.fd w.2.1}"
    | _ => throw "rule: matched node differs"
    set { w with atoms := rest, atomIdx := w.atomIdx + 1, σ := σ, ρ := ρ, μ := μ }
    let i ← instOf f ic.toList n (some w.atomIdx)
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
  | .rest _ => throw "rule: a rest variable that is no argument"
  | .rep _ _ => throw "rule: a repeated argument that is no argument"
  | .times _ _ => throw "rule: a repeated argument that is no argument"
  | .count _ => throw "rule: a count matched"
  | .lit s v => do
    let w ← get
    match w.atoms with
    | (n, "#lit", _, _) :: rest =>
      match w.S.defOf n with
      | some (.lit s' v') =>
        if s' == s && v' == v then set { w with atoms := rest, atomIdx := w.atomIdx + 1 }; pure (n, n)
        else throw "rule: literal differs"
      | _ => throw "rule: literal differs"
    | _ => throw "rule: no line for a literal"
  | .app f ps => walkQs ps >>= walkApp (key (.app f ps)) f ps

/-- The matched node and instance of each argument that is no variable. -/
def walkQs : List Pat → WalkM P (List (Option (Nat × Nat)))
  | [] => pure []
  | .var _ :: rest => walkQs rest >>= fun r => pure (none :: r)
  | .rest _ :: rest => walkQs rest >>= fun r => pure (none :: r)
  -- A repeated argument is matched once.
  | .rep (.var _) _ :: rest => walkQs rest >>= fun r => pure (none :: r)
  | .rep (.rest _) _ :: _ => throw "rule: a repeated rest variable"
  | .rep (.rep _ _) _ :: _ => throw "rule: a repeated argument repeated"
  | .rep (.times _ _) _ :: _ => throw "rule: a repeated argument repeated"
  | .rep (.count _) _ :: _ => throw "rule: a repeated argument repeated"
  | .count _ :: _ => throw "rule: a count matched"
  | .times (.var _) _ :: rest => walkQs rest >>= fun r => pure (none :: r)
  | .times (.rest _) _ :: _ => throw "rule: a repeated rest variable"
  | .times (.rep _ _) _ :: _ => throw "rule: a repeated argument repeated"
  | .times (.times _ _) _ :: _ => throw "rule: a repeated argument repeated"
  | .times (.count _) _ :: _ => throw "rule: a repeated argument repeated"
  | .times (.lit s v) _ :: rest =>
    walkQ (.lit s v) >>= fun x => walkQs rest >>= fun r => pure (some x :: r)
  | .times (.app f qs) _ :: rest =>
    walkQ (.app f qs) >>= fun x => walkQs rest >>= fun r => pure (some x :: r)
  | .rep (.lit s v) _ :: rest =>
    walkQ (.lit s v) >>= fun x => walkQs rest >>= fun r => pure (some x :: r)
  | .rep (.app f qs) _ :: rest =>
    walkQ (.app f qs) >>= fun x => walkQs rest >>= fun r => pure (some x :: r)
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

/-- The sort and spelling of node `n`, when it is a literal. -/
def litOfNode (S : St P) (n : Nat) : Option (String × String) :=
  match S.defOf n with
  | some (.lit s v) => some (s, v)
  | _ => none

/-- The primitive `f` applied to the instances of its arguments, which are
the literal nodes `args.map (·.1)`, when it computes the literal node `out`
(`primOk`): the application to the literals is `out` by the kernel's `prim`
step, and the instance is that application argument by argument. -/
def primInst (S : St P) (f : String) (args : List (Nat × Nat)) (out : Nat) : St P × Option Nat :=
  match (args.map (·.1)).mapM (litOfNode S), litOfNode S out with
  | some lits, some o =>
    if !primOk f lits o then (S, none)
    else
      match intern S (.app f (args.map (·.1))) with
      | (S, some pn) =>
        let (S, st) := emit S (.prim f pn out) pn out
        let S := S.mergeBy pn out (some (some st))
        match intern S (.app f (args.map (·.2))) with
        | (S, some i) =>
          if i == pn then (S, some i)
          else
            let (S, p) := congStep S f i pn
            (S.mergeBy i pn p, some i)
        | (S, none) => (S, none)
      | (S, none) => (S, none)
  | _, _ => (S, none)

/-- The built primitive application `f` of the built arguments `cs` against
the next `b` node, the literal the engine computed. -/
def builtPrim (f : String) (cs : List (Nat × Nat)) : WalkM P (Nat × Nat) := do
  let w ← get
  match w.rhs with
  | (n, _) :: rest =>
    set { w with rhs := rest }
    match ← withS fun S => primInst S f cs n with
    | some i => pure (n, i)
    | none => throw "rule: primitive computes another value"
  | [] => throw "rule: no node for a computed literal"

/-- The literal that spells the count of the multiplicity variable `k`. -/
def groundCount (k : String) : WalkM P (Nat × Nat) := do
  match (← get).μ.lookup k with
  | some n =>
    match ← withS fun S => intern S (.lit "i64" (toString n)) with
    | some i => pure (i, i)
    | none => throw "rule: count literal ill-sorted"
  | none => throw "rule: unbound multiplicity variable"

/-- A primitive application the stream has no node for (a guard, or an
argument of one): its value is computed here from its arguments' literals,
and it is that literal by the kernel's `prim` step. -/
def groundPrim (f : String) (args : List (Nat × Nat)) : WalkM P (Nat × Nat) := do
  let S := (← get).S
  let some (_, res) := primSig f | throw "rule: not a primitive"
  let some lits := (args.map (·.1)).mapM (litOfNode S) | throw "rule: primitive on a node that is no literal"
  let some vals := lits.mapM (fun a => Val.parse a.1 a.2) | throw "rule: literal without a value"
  let some v := primEval f vals | throw "rule: primitive has no value"
  let some text := v.spell | throw "rule: computed value without a spelling"
  let some out ← withS fun S => intern S (.lit res text) | throw "rule: computed literal ill-sorted"
  match ← withS fun S => primInst S f args out with
  | some i => pure (out, i)
  | none => throw "rule: primitive computes another value"

mutual

/-- The node and the instance of a pattern the stream writes no line for, from
the assignment alone: a bound variable, a literal, or a primitive applied to
such. -/
def groundP (p : Pat) : WalkM P (Nat × Nat) :=
  match p with
  | .var x => do
    match (← get).σ.lookup x with
    | some n => pure (n, n)
    | none => throw "rule: unbound variable"
  | .lit s v => do
    match ← withS fun S => intern S (.lit s v) with
    | some n => pure (n, n)
    | none => throw "rule: literal ill-sorted"
  | .app f ps => groundPs ps >>= groundPrim f
  | .rest _ => throw "rule: a rest variable that is no argument"
  | .rep _ _ => throw "rule: a repeated argument that is no argument"
  | .times _ _ => throw "rule: a repeated argument that is no argument"
  | .count k => groundCount k

def groundPs : List Pat → WalkM P (List (Nat × Nat))
  | [] => pure []
  | p :: ps => groundP p >>= fun x => groundPs ps >>= fun r => pure (x :: r)

end

/-- The built application `f` of counted built arguments against the next `b`
node, which is the counted node itself. -/
def builtAppC (f : String) (cks : List ((Nat × Nat) × Nat)) : WalkM P (Nat × Nat) := do
  let w ← get
  match w.rhs with
  | (n, _) :: rest =>
    set { w with rhs := rest }
    match ← withS fun S => intern S (countedNode f (cks.map fun x => (x.1.2, x.2))) with
    | some i => if i == n then pure (n, i) else throw "rule: built counted node differs"
    | none => throw "rule: instance ill-sorted"
  | [] => throw "rule: no node for a built application"

/-- Whether an argument list holds a count above the kernel's limit. -/
def bigCount (ps : List Pat) : Bool :=
  ps.any fun p => match p with
    | .times _ n => n > Ctx.countLimit
    | _ => false

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
  | .rep _ _ => throw "rule: a repeated argument that is no argument"
  | .times _ _ => throw "rule: a repeated argument that is no argument"
  | .count k => groundCount k
  | .rest _ => throw "rule: a rest variable that is no argument"
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
      -- A primitive application's `b` node is the literal the engine computed;
      -- its arguments have none.
      | none =>
        if (primSig f).isSome then groundPs ps >>= builtPrim f
        else if bigCount ps then walkBsC ps >>= builtAppC f
        else walkBs ps >>= builtApp f

/-- The built arguments with their counts, none repeated: for an argument
list with a count above the kernel's limit. -/
def walkBsC : List Pat → WalkM P (List ((Nat × Nat) × Nat))
  | [] => pure []
  | .times (.var x) n :: ps =>
    walkB (.var x) >>= fun y => walkBsC ps >>= fun r => pure ((y, n) :: r)
  | .times (.lit s v) n :: ps =>
    walkB (.lit s v) >>= fun y => walkBsC ps >>= fun r => pure ((y, n) :: r)
  | .times (.app f qs) n :: ps =>
    walkB (.app f qs) >>= fun y => walkBsC ps >>= fun r => pure ((y, n) :: r)
  | .times (.rest _) _ :: _ => throw "rule: a repeated rest variable"
  | .times (.rep _ _) _ :: _ => throw "rule: a repeated argument repeated"
  | .times (.times _ _) _ :: _ => throw "rule: a repeated argument repeated"
  | .times (.count _) _ :: _ => throw "rule: a repeated argument repeated"
  | .var x :: ps => walkB (.var x) >>= fun y => walkBsC ps >>= fun r => pure ((y, 1) :: r)
  | .lit s v :: ps => walkB (.lit s v) >>= fun y => walkBsC ps >>= fun r => pure ((y, 1) :: r)
  | .app f qs :: ps => walkB (.app f qs) >>= fun y => walkBsC ps >>= fun r => pure ((y, 1) :: r)
  | .count k :: ps => groundCount k >>= fun y => walkBsC ps >>= fun r => pure ((y, 1) :: r)
  | .rest _ :: _ => throw "rule: a rest variable beside a count above the limit"
  | .rep _ _ :: _ => throw "rule: a multiplicity variable beside a count above the limit"

def walkBs : List Pat → WalkM P (List (Nat × Nat))
  | [] => pure []
  -- A rest variable gives the nodes it is bound to, each its own instance.
  | .rest x :: ps => do
    match (← get).ρ.lookup x with
    | some ys => walkBs ps >>= fun r => pure (ys.map (fun y => (y, y)) ++ r)
    | none => throw "rule: unbound rest variable"
  -- A repeated argument gives its node as many times as its count.
  | .rep (.var x) k :: ps => do
    match (← get).μ.lookup k with
    | some n => walkB (.var x) >>= fun y => walkBs ps >>= fun r => pure (List.replicate n y ++ r)
    | none => throw "rule: unbound multiplicity variable"
  | .rep (.lit s v) k :: ps => do
    match (← get).μ.lookup k with
    | some n => walkB (.lit s v) >>= fun y => walkBs ps >>= fun r => pure (List.replicate n y ++ r)
    | none => throw "rule: unbound multiplicity variable"
  | .rep (.app f qs) k :: ps => do
    match (← get).μ.lookup k with
    | some n => walkB (.app f qs) >>= fun y => walkBs ps >>= fun r => pure (List.replicate n y ++ r)
    | none => throw "rule: unbound multiplicity variable"
  | .rep (.rest _) _ :: _ => throw "rule: a repeated rest variable"
  | .rep (.rep _ _) _ :: _ => throw "rule: a repeated argument repeated"
  | .rep (.times _ _) _ :: _ => throw "rule: a repeated argument repeated"
  | .rep (.count _) _ :: _ => throw "rule: a repeated argument repeated"
  -- An argument with a fixed count is built once.
  | .times (.var x) n :: ps =>
    walkB (.var x) >>= fun y => walkBs ps >>= fun r => pure (List.replicate n y ++ r)
  | .times (.lit s v) n :: ps =>
    walkB (.lit s v) >>= fun y => walkBs ps >>= fun r => pure (List.replicate n y ++ r)
  | .times (.app f qs) n :: ps =>
    walkB (.app f qs) >>= fun y => walkBs ps >>= fun r => pure (List.replicate n y ++ r)
  | .times (.rest _) _ :: _ => throw "rule: a repeated rest variable"
  | .times (.rep _ _) _ :: _ => throw "rule: a repeated argument repeated"
  | .times (.times _ _) _ :: _ => throw "rule: a repeated argument repeated"
  | .times (.count _) _ :: _ => throw "rule: a repeated argument repeated"
  | .count k :: ps => groundCount k >>= fun y => walkBs ps >>= fun r => pure (y :: r)
  | .var x :: ps => walkB (.var x) >>= fun y => walkBs ps >>= fun r => pure (y :: r)
  | .lit s v :: ps => walkB (.lit s v) >>= fun y => walkBs ps >>= fun r => pure (y :: r)
  | .app f qs :: ps => walkB (.app f qs) >>= fun y => walkBs ps >>= fun r => pure (y :: r)

end

/-- One side of a body equality: a bound variable's node, a matched pattern's
node and instance, or `none` for a variable not bound yet. -/
def side (p : Pat) : WalkM P (Option (Nat × Nat)) := do
  -- A primitive application has no line: it is computed from the assignment.
  if let .app f _ := p then
    if (primSig f).isSome then return some (← groundP p)
  -- A literal the stream writes no line for.
  if let .lit _ _ := p then
    let lined := match (← get).atoms with
      | (_, "#lit", _, _) :: _ => true
      | _ => false
    if !lined then return some (← groundP p)
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
        | (_, h, cs, _) :: _ => g == h && k.all (· == units cs)
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
  ρ : List (String × List Nat)
  μ : List (String × Nat)
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
  for x in r.rests do
    match w.ρ.lookup x, r.sorts.lookup x with
    | some ns, some s =>
      if ns.any (fun n => sortOf w.S n != some s) then throw "rule: rest variable of another sort"
    | _, _ => throw "rule: unbound rest variable"
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
  pure { nl, il, nr, ir, σ := (← get).σ, ρ := (← get).ρ, μ := (← get).μ, prems := prems.map (·.toList) }

mutual

/-- The node that is the term `t` over atoms, added to the table when it is
not there. -/
def addS (S : St P) : STm → St P × Option Nat
  | .atom (.node n) => (S, some n)
  | .atom (.lit s v) => intern S (.lit s v)
  | .app f args =>
    match addSs S args with
    | (S, some ids) => intern S (.app f ids)
    | (S, none) => (S, none)

def addSs (S : St P) : List STm → St P × Option (List Nat)
  | [] => (S, some [])
  | t :: ts =>
    match addS S t with
    | (S, some i) =>
      match addSs S ts with
      | (S, some is) => (S, some (i :: is))
      | (S, none) => (S, none)
    | (S, none) => (S, none)

end

mutual

/-- The applications in `t` of a sequence operator to one argument, each with
that argument (the engine builds the argument in the application's place),
and those to no argument, which the engine builds as the unit. -/
def singlesS (isSeq : String → Bool) : STm → List (STm × STm)
  | .atom _ => []
  | .app f args =>
    (match args with
      | [x] => if isSeq f then [(STm.app f [x], x)] else []
      -- No argument: listed with itself, for the unit.
      | [] => if isSeq f then [(STm.app f [], STm.app f [])] else []
      | _ => []) ++ singlesSs isSeq args

def singlesSs (isSeq : String → Bool) : List STm → List (STm × STm)
  | [] => []
  | t :: ts => singlesS isSeq t ++ singlesSs isSeq ts

end

mutual

/-- A program term as a term over atoms. -/
def termS : Term → STm
  | .lit s v => .atom (.lit s v)
  | .app f args => .app f (termsS args)

def termsS : List Term → List STm
  | [] => []
  | t :: ts => termS t :: termsS ts

end

/-- What the `q` lines of a sequence rule's firing give: the root node, the
binding, and per filter the member of each element's class that matched. -/
structure SeqRead where
  root : Option Nat := none
  B : SBind := {}
  members : List (String × List Nat) := []
  /-- The name the next `qv` lines belong to: a column or a scalar. -/
  lits : Option (String × Bool) := none
  ok : Bool := true

/-- Reads the binding lines of rule `r`'s firing. A class with a count `c:k`
is `k` arguments of a rest sequence, and the count `k` of a filter's element. -/
def readSeq (S : St P) (r : SeqRule) (lines : List (List String)) : SeqRead :=
  let rests := r.items.filterMap fun it => match it with | .rest x => some x | _ => none
  let entry (w : String) : Option (Nat × Nat) :=
    match w.splitOn ":" with
    | [c] => (S.node? c).map (·, 1)
    | [c, k] => (S.node? c).bind fun c => k.toNat?.map (c, ·)
    | _ => none
  let push (xs : List (String × List SAtom)) (x : String) (a : SAtom) : List (String × List SAtom) :=
    match xs.lookup x with
    | some l => (xs.filter (·.1 != x)) ++ [(x, l ++ [a])]
    | none => xs ++ [(x, [a])]
  lines.foldl (fun (R : SeqRead) ws =>
    match ws with
    | ["q", n] => { R with root := S.node? n, ok := R.ok && (S.node? n).isSome }
    | "qf" :: name :: es =>
      match es.mapM entry with
      | some xs => { R with B := { R.B with counts := R.B.counts ++ [(name, xs.map (·.2))] } }
      | none => { R with ok := false }
    | "qe" :: name :: ms =>
      match ms.mapM S.node? with
      | some xs => { R with members := R.members ++ [(name, xs)] }
      | none => { R with ok := false }
    | "qn" :: name :: vs =>
      match vs.mapM entry with
      | some xs =>
        if rests.contains name then
          { R with B := { R.B with seqs := R.B.seqs ++
              [(name, xs.flatMap fun (c, k) => List.replicate k (SAtom.node c))] } }
        else { R with B := { R.B with cols := R.B.cols ++ [(name, xs.map fun (c, _) => SAtom.node c)] } }
      | none => { R with ok := false }
    | ["ql", name] => { R with lits := some (name, false), B := { R.B with cols := R.B.cols ++ [(name, [])] } }
    | ["qt", name] => { R with lits := some (name, true) }
    | "qv" :: v =>
      match R.lits with
      | some (name, scalar) =>
        match r.sorts.lookup name with
        | some sort =>
          let a := SAtom.lit sort (" ".intercalate v)
          if scalar then { R with B := { R.B with scalars := R.B.scalars ++ [(name, a)] } }
          else { R with B := { R.B with cols := push R.B.cols name a } }
        | none => { R with ok := false }
      | none => { R with ok := false }
    | ["qs", name, v] =>
      match S.node? v with
      | some n => { R with B := { R.B with scalars := R.B.scalars ++ [(name, .node n)] } }
      | none => { R with ok := false }
    -- A filter's counts are on its `qf` line.
    | "qk" :: _ => R
    -- A multiplicity scalar: not read yet.
    | _ => { R with ok := false }) {}

/-- The kernel steps of a sequence rule's firing under the binding `B`, which
merged the node `new` it built with `root`: the `seq` step proves the rule's
two terms equal; each element's pattern instance is its member argument by
argument; an application of a sequence operator to one argument is that
argument; the left term is then `root` and the right term `new` under the
operators' laws. -/
def seqFinish (S : St P) (od j : Nat) (r : SeqRule) (B : SBind) (members : List (String × List Nat))
    (root new : Nat) : St P := Id.run do
  let some (L, T) := seqApply r B
    | return S.fail s!"sequence rule: no instance under the binding | left {(match r.lhs with | some p => (patB B (B.look none) p).isSome | none => (itemsArgs B r.items).isSome)}, right {(rhsS r B {} r.rhs).isSome}, binding {repr B}, rule {repr r.rhs}"
  let (S, a) := addS S L
  let (S, b) := addS S T
  let (some a, some b) := (a, b) | return S.fail "sequence rule: instance ill-sorted"
  let (S, st) := emit S (.seq od j B a b) a b
  let mut S := S
  -- Each element's instance is its member.
  for it in r.items do
    if let .filter name p := it then
      if let (some ms, .app g _) := (members.lookup name, p) then
        for (m, i) in ms.zipIdx do
          if let some t := patB B (B.look (some i)) p then
            let (S1, ti) := addS S t
            S := S1
            if let some ti := ti then
              if S.fd ti != S.fd m then
                let (S1, pf) := congStep S g ti m
                S := S1.mergeBy ti m pf
  -- An application to one argument is that argument.
  for (t, x) in (singlesS (fun f => (S.prog.kind f).isAssoc) T).reverse do
    let (S1, ti) := addS S t
    let (S1, xi) := addS S1 x
    S := S1
    if let (some ti, some xi, .app f as) := (ti, xi, t) then
      if as.isEmpty then
        -- The application to no argument is the unit, by the `unit` step.
        if let some u := S.unit f then
          if S.fd ti != S.fd u then
            let (S1, st) := emit S (.unit f ti u) ti u
            S := S1.mergeBy ti u (some (some st))
      else if S.fd ti != S.fd xi then
        let (S1, pf) := congStepL S f ti xi
        S := S1.mergeBy ti xi pf
  let f := match L with
    | .app f _ => f
    | .atom _ => r.op
  let (S1, p1) := congStepL S f root a
  let (S1, p2) : St P × Pf := match T with
    | .app g _ => congStepL S1 g b new
    | .atom _ => eqP S1 b new
  -- A `:flatten` match that read one root argument through a member of its
  -- class: the member is the application of the bound arguments no other root
  -- argument answers, built here and found in that argument's class. The root
  -- is then the root with the member in the argument's place, argument by
  -- argument, which is the left term under the operator's laws.
  let (S1, p1) : St P × Pf := Id.run do
    if p1.isSome then return (S1, p1)
    let S := S1
    let (some (.app _ rootArgs), some (.app _ bound)) := (S.defOf root, S.defOf a) | return (S, none)
    let (opened, left) := rootArgs.foldl (fun (acc : List Nat × List Nat) r =>
      match acc.2.find? (fun x => S.fd x == S.fd r) with
      | some x => (acc.1, acc.2.erase x)
      | none => (acc.1 ++ [r], acc.2)) ([], bound)
    let [o] := opened | return (S, none)
    if left.isEmpty then return (S, none)
    let (S, m) := appNode S f left
    let some m := m | return (S, none)
    if S.fd m != S.fd o then return (S, none)
    let (S, root2) := appNode S f (rootArgs.map fun r => if r == o then m else r)
    let some root2 := root2 | return (S, none)
    let (S, pa) := congStep S f root root2
    let (S, pb) := congStepL S f root2 a
    if pa.isNone || pb.isNone then return (S, none)
    transP S root a pa pb
  if p1.isNone then return S1.fail "sequence rule: left side is not the root node"
  if p2.isNone then return S1.fail "sequence rule: right side is not the built node"
  let (S1, q) := transP S1 root b p1 (some (some st))
  let (S1, q) := transP S1 root new q p2
  return S1.mergeBy root new q

/-- A firing of a sequence rule whose left side is a pattern: the `e` lines
give the match, as for a rule, and the binding is read from it (a variable
bound to a literal node is that literal; a rest variable's nodes in order; a
multiplicity variable's count). -/
def seqFireP (S : St P) (od j : Nat) (r : SeqRule) (p : Pat) (x y : Nat) : St P :=
  let (atoms, rhs) := (S.atoms.toList, S.rhs)
  let (res, w) := ((walkQ p).run).run { S := S, atoms, rhs }
  let S := w.S
  match res with
  | .error e => S.fail e
  | .ok (nl, il) =>
    let atomOf (n : Nat) : SAtom := match S.defOf n with
      | some (.lit s v) => .lit s v
      | _ => .node n
    let B : SBind := { scalars := w.σ.map fun (v, n) => (v, atomOf n),
                       -- A rest variable is named with its dots in a pattern, and
                       -- without them as a comprehension's source.
                       seqs := w.ρ.flatMap fun (v, ns) =>
                         [(v, ns.map SAtom.node), ((v.drop 2).toString, ns.map SAtom.node)],
                       kcounts := w.μ }
    let new := if S.fd nl == S.fd x then y else x
    seqFinish S od j r B [] il new

/-- A sequence rule's firing, which merged `new`, the node it built, with the
root node. The `seq` step proves the rule's two terms under the binding
equal; each element's pattern instance is its member argument by argument;
the left term is then the root and the right term the built node under the
operators' laws. -/
def seqFire (S : St P) (o : Nat) (x y : Nat) : St P := Id.run do
  let lines := S.seqLines
  let S := { S with seqLines := [] }
  let skip (S : St P) : St P :=
    let kind := "rewrite:sequence-rule"
    { S with unchecked := S.unchecked.insert kind (S.unchecked.getD kind 0 + 1) }
  let some (od, .seq [some r]) := ((S.prog.decls.filter (·.1 ≤ o)).getLast? : Option (Nat × Decl))
    | return skip S
  let R := readSeq S r lines
  let some root := R.root | return S.fail "sequence rule: binding unreadable"
  if !R.ok then return skip S
  let new := if x == root then y else x
  return seqFinish S od 0 r R.B R.members root new

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
    match id.toNat?, idsC S kids with
    | some i, some cks => define S i (countedNode f cks)
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
  | ["y", c, m, k] =>
    match S.node? c, S.node? m, k.toNat? with
    | some c, some m, some k =>
      { S with regroups := S.regroups ++ [(k, c, m)], events := S.events - 1 }
    | _, _, _ => S.fail "regroup: unreadable"
  | ["s", c, m, k, p, at_] =>
    match S.node? c, S.node? m, k.toNat?, at_.toNat? with
    | some c, some m, some k, some at_ =>
      if p == "-" then
        { S with opens := S.opens ++ [(k, c, m, none, at_)], events := S.events - 1 }
      else match p.toNat? with
        | some p => { S with opens := S.opens ++ [(k, c, m, some p, at_)], events := S.events - 1 }
        | none => S.fail "splice: unreadable"
    | _, _, _, _ => S.fail "splice: unreadable"
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
        | some (.app f as) =>
          -- A comb: the two nodes read through the comb are in one class
          -- position by position (an application to one argument is it).
          if (S.prog.kind f).isFold then
            let left := S.prog.kind f == .foldL
            let own (z : Nat) : List Nat := match S.defOf z with
              | some (.app g cs) => if g == f then cs else [z]
              | _ => [z]
            let same (l m : List Nat) : Bool :=
              l.length == m.length && (l.zip m).all fun (c, d) => S.fd c == S.fd d
            same (own x) (own y) || same (kviewF S f left x) (kviewF S f left y)
          else spells S y f as
        | _ => false
      if one a b || one b a then
        -- The operator of the node whose arguments normalize to the other.
        let f := match S.defOf a, S.defOf b with
          | some (.app f _), _ => if one a b then f else
              (match S.defOf b with | some (.app g _) => g | _ => f)
          | _, some (.app g _) => g
          | _, _ => ""
        let (S, p) := congStepL S f a b
        let (S, p) := if p.isSome then (S, p) else invDirect S f a b
        let (S, p) := if p.isSome then (S, p) else
          (let (S, q) := invDirect S f b a; symmP S b a q)
        -- An argument that is itself an application of `f` and stands for its
        -- class, which the line's splice witness reads through another
        -- member: the node with the member in the argument's place, argument
        -- by argument, is the other node under `f`'s laws.
        let viaSplice (S : St P) (x y : Nat) : St P × Pf :=
          match S.defOf x with
          | some (.app _ xs) =>
            match S.splices.find? (fun (cm : Nat × Nat) => xs.any fun a => S.fd a == S.fd cm.1 && a != cm.2) with
            | some (c, m) =>
              match appNode S f (xs.map fun a => if S.fd a == S.fd c then m else a) with
              | (S, some x2) =>
                let (S, p1) := congStep S f x x2
                let (S, p2) := congStepL S f x2 y
                if p1.isNone || p2.isNone then (S, none) else transP S x y p1 p2
              | (S, none) => (S, none)
            | none => (S, none)
          | _ => (S, none)
        let (S, p) := if p.isSome then (S, p) else viaSplice S a b
        let (S, p) := if p.isSome then (S, p) else
          (let (S, q) := viaSplice S b a; symmP S b a q)
        -- An argument that is an application of `f` and stands for the class
        -- of one of the other node's arguments: the node with that argument
        -- in its place, argument by argument, is the other node under `f`'s
        -- laws.
        let viaArgs (S : St P) (x y : Nat) : St P × Pf :=
          match S.defOf x, S.defOf y with
          | some (.app _ xs), some (.app g ys) =>
            if g != f then (S, none)
            else
              match appNode S f (xs.map fun a => (ys.find? fun d => S.fd d == S.fd a).getD a) with
              | (S, some x2) =>
                if x2 == x then (S, none)
                else
                  let (S, p1) := congStep S f x x2
                  let (S, p2) := congStepL S f x2 y
                  if p1.isNone || p2.isNone then (S, none) else transP S x y p1 p2
              | (S, none) => (S, none)
          | _, _ => (S, none)
        let (S, p) := if p.isSome then (S, p) else viaArgs S a b
        let (S, p) := if p.isSome then (S, p) else
          (let (S, q) := viaArgs S b a; symmP S b a q)
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
    | some o => { S with fire := some (o, kind == "w"), atoms := #[], rhs := [], seqLines := [], events := S.events - 1 }
    | none => S.fail "rule: unreadable"
  | "e" :: id :: f :: kids =>
    match S.node? id, atomArgs S kids with
    | some i, some (fixed, groups) =>
      { S with atoms := S.atoms.push (i, f, fixed, groups), events := S.events - 1 }
    | _, _ => S.fail "rule: unreadable"
  | "b" :: xs =>
    let one (x : String) : Option (Nat × Bool) :=
      if x.startsWith "g" then (S.node? (x.drop 1).toString).map (·, true) else (S.node? x).map (·, false)
    match xs.mapM one with
    | some r => { S with rhs := r, events := S.events - 1 }
    | none => S.fail "rule: unreadable"
  | ["m", j, a, b] =>
    -- A sequence rule's firing: its binding is read, and not checked yet.
    if !S.seqLines.isEmpty then
      match S.node? a, S.node? b, S.fire with
      | some a, some b, some (o, _) =>
        let S := seqFire S o a b
        { S with splices := [], opens := [], regroups := [], inverses := [] }
      | _, _, _ => S.fail "sequence rule: unreadable"
    else
    match j.toNat?, S.node? a, S.node? b, S.fire with
    | some j, some a, some b, some (o, rw) =>
      -- The engine cites a rule by an offset inside its command.
      match ((S.prog.decls.filter (·.1 ≤ o)).getLast? : Option (Nat × Decl)) with
      | some (od, Decl.seq rs) =>
        match rs[j]? with
        | some (some sr) =>
          -- A `rule` is matched through its body, a `rewrite` through its left side.
          match sr.body.orElse fun _ => sr.lhs with
          | some p => seqFireP S od j sr p a b
          | none => S.fail "sequence rule: no binding"
        | _ => S.fail s!"rule: outside the reader's language | {od} {j}"
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
                  let (S, st) := emit S (.rule od j fr.σ (fr.ρ.map fun (xn : String × List Nat) => (xn.1, xn.2.map fun n => (n, 1))) fr.μ prems fr.il fr.ir) fr.il fr.ir
                  let (S, p1) := eqP S x fr.il
                  let (S, p2) := eqP S fr.ir y
                  let (S, q) := transP S x fr.ir p1 (some (some st))
                  transP S x y q p2
                | none => (S, none)
              S.mergeBy x y pf
            else S.fail "rule: merged nodes differ"
          | .error e => S.fail e
        | _ => S.fail s!"rule: outside the reader's language | {od} {j}"
      | _ => S.fail "rule: no such command"
    | _, _, _, _ => S.fail "rule: unreadable"
  | ["g", off, a, b] =>
    match off.toNat?, S.node? a, S.node? b with
    | some o, some a, some b =>
      match S.declAt[o]? with
      | some (.goal l r) =>
        -- A term's node, with nested applications read through (as written
        -- in place) or not (as `let` names).
        let is (t : Term) (n : Nat) : Bool := eval S t == some n || evalN S t == some n
        if is l a && is r b then
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
        else
          -- The stream's nodes are not what the terms evaluate to as read
          -- here (a nested application written in place beside one named by
          -- a `let`). The kernel's goal step needs the terms only: each term,
          -- as the kernel interns it, is the stream's node under its
          -- operator's laws, whatever the grouping; the two nodes are in one
          -- class.
          if S.fd a != S.fd b then S.fail "goal: not in one class"
          else
            let side (S : St P) (t : Term) (n : Nat) : St P × Option (Nat × Pf) :=
              -- The term's node, added to the table when it is not there.
              -- Only under a sequence operator can the two readings differ:
              -- elsewhere the stream's node is the term's or the line is wrong.
              -- A term that evaluates to the stream's node as read here.
              if eval S t == some n || evalN S t == some n then
                match writtenP S t with
                | (S, some (tn, _, p)) => (S, some (tn, p))
                | (S, none) => (S, none)
              else
              match t with
              | .app f _ =>
                if !((S.prog.kind f).isAssoc || (S.prog.kind f).isFold) then (S, none)
                else
                  match addS S (termS t) with
                  | (S, some tn) => let (S, p) := congStepL S f tn n; (S, some (tn, p))
                  | (S, none) => (S, none)
              | .lit _ _ => (S, none)
            match side S l a with
            | (S, some (tl, pl)) =>
              match side S r b with
              | (S, some (tr, pr)) =>
                if pl.isNone || pr.isNone then S.fail "goal: its terms differ"
                else
                  let S := { S with proved := o :: S.proved }
                  let (S, q) := eqP S a b
                  let (S, q) := transP S tl b pl q
                  let (S, pr') := symmP S tr b pr
                  let (S, q) := transP S tl tr q pr'
                  match stepOf S tl q with
                  | (S, some st) => (S.withCore fun c => c.goal o l r st).1
                  | (S, none) => S
              | (S, none) => S.fail "goal: its terms differ"
            | (S, none) => S.fail "goal: its terms differ"
      | _ => S.fail "goal: no such command"
    | _, _, _ => S.fail "goal: unreadable"
  -- A cancellative operator's lattice merge, with the combination of node
  -- equations the two classes differ by.
  | "k" :: a :: b :: npos :: rest =>
    match S.node? a, S.node? b, npos.toNat?, rest.mapM (fun (x : String) => x.toNat?) with
    | some a, some b, some np, some fs =>
      let rec pairs : List Nat → Option (List (Nat × Nat))
        | [] => some []
        | n :: q :: r => (S.node? (toString n)).bind fun n => (pairs r).map ((n, q) :: ·)
        | [_] => none
      match pairs fs with
      | some ps =>
        match latticeP S a b (ps.take np) (ps.drop np) with
        | (S, some p) => S.mergeBy a b (some p)
        | (S, none) => S
      | none => S.fail "lattice: unreadable"
    | _, _, _, _ => S.fail "lattice: unreadable"
  | "i" :: a :: b :: n :: rest =>
    match S.node? a, S.node? b, S.node? n, (rest.mapM (fun (x : String) => x.toNat?)).bind (rules S) with
    | some a, some b, some n, some rs =>
      -- The derivation is computed first, on classes the state shares; the
      -- kernel steps are emitted after, when the state is held once again.
      -- A sequence operator: one rule, applied to a run of the node's arguments.
      let seqOp : Option String := match S.defOf n with
        | some (.app f _) =>
          if S.prog.kind f == .assoc || (S.prog.kind f).isFold then some f else none
        | _ => none
      if let some f := seqOp then
        match rs with
        | [(l, r, _)] =>
          let other := if n == a then b else a
          match seqReduce S f n other l r with
          | (S, some p) => S.mergeBy n other (some p)
          | (S, none) => S.fail "completion: rule does not apply to the sequence"
        | _ => S.fail "completion: a sequence rewrite takes one rule"
      else
      match interReduce S S.atRound a b n rs with
      | .ok c =>
        let (S, r) := emitChain S c
        match r with
        | some (start, target, pf) =>
          -- The start is in the class of the merged node that is not the target.
          let other := if target == a then b else a
          let (S, q) := eqP S other start
          let (S, q) := transP S other target q pf
          -- With no derivation step: the line's node, which is in one of the
          -- two classes, holds an inverse pair and is the other node.
          if q.isSome then S.mergeBy other target q
          else invTry S n (if S.fd n == S.fd a then b else a)
        | none => invTry S n (if S.fd n == S.fd a then b else a)
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
                  let (S, r1) := emitChain S ca
                  let (S, r2) := emitChain S cb
                  let (S, q) := eqP S a b
                  if q.isNone then
                    S.fail s!"completion: sides do not join after the cancellation | kept {nl} {nr}, lost {ng}, chains {r1.map fun x => (x.1, x.2.1, x.2.2.isSome)} {r2.map fun x => (x.1, x.2.1, x.2.2.isSome)}, classes of a b {S.fd a} {S.fd b}, of kept {S.fd nl} {S.fd nr}, of chain ends {r1.map fun x => S.fd x.2.1} {r2.map fun x => S.fd x.2.1}, left chain first {ca.first} peak {ca.peak} steps {ca.steps.toList.map fun st => (st.l, st.r, st.q, st.rest, st.after, st.atom)}, defs {(ca.steps.toList.map fun st => (repr (S.defOf st.l), repr (S.defOf st.r)))}, left {left} right {right} gone {gone}"
                  else S.mergeBy a b q
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
      { S with snaps := (S.snaps.extract 0 d).push (S.cid.size, S.plain, S.spell, S.invIn) }
    | _ => S.fail "mark: unreadable"
  | ["restore", d] =>
    match d.toNat? with
    | some (d + 1) =>
      match S.snaps[d]?, S.withCore fun c => c.restore d (d + 1) with
      | some (n, pl, sp, iv), (S, true) =>
        -- The engine's ids past the mark are free again; the table keeps its
        -- nodes, and the kernel steps checked since stay true.
        { S with cid := S.cid.extract 0 n, plain := pl, spell := sp, invIn := iv,
                 snaps := S.snaps.extract 0 (d + 1), fire := none }
      | _, (S, _) => S.fail "restore: no such mark"
    | _ => S.fail "restore: unreadable"
  | ["rpop", d] =>
    match d.toNat? with
    | some d =>
      match S.snaps[d]?, S.withCore fun c => c.restore d d with
      | some (n, pl, sp, iv), (S, true) =>
        { S with cid := S.cid.extract 0 n, plain := pl, spell := sp, invIn := iv,
                 snaps := S.snaps.extract 0 d, fire := none }
      | _, (S, _) => S.fail "restore: no such mark"
    | none => S.fail "restore: unreadable"
  | "u" :: kind :: rest =>
    -- An event the stream gives no witness for: counted, and nothing is merged.
    let _ := rest
    { S with unchecked := S.unchecked.insert kind (S.unchecked.getD kind 0 + 1), splices := [], opens := [], regroups := [], inverses := [] }
  | [""] => { S with events := S.events - 1 }
  | q :: rest =>
    -- The binding of a sequence rule's firing: kept for its `m` line.
    if ["q", "qf", "qe", "qn", "ql", "qv", "qk", "qs", "qt", "qm"].contains q then
      { S with seqLines := S.seqLines ++ [q :: rest], events := S.events - 1 }
    else S.fail "unreadable line"
  | _ => S.fail "unreadable line"

/-- Replays one line. The witness lines (`s`, `j`) hold until the next line
of another kind has been replayed. -/
def step (S : St P) (line : String) : St P :=
  let before := S.nFailed
  let S := stepCore S line
  let S := if S.logFailed && S.nFailed > before then
      let entry := toString S.events ++ "\t" ++ (S.lastCause.splitOn " | ").headD "" ++ "\t" ++ line ++ "\n"
      { S with failedLog := S.failedLog.push entry }
    else S
  if line.startsWith "s " || line.startsWith "j " || line.startsWith "y " then S
  else { S with splices := [], opens := [], regroups := [], inverses := [] }

def start (P : Program) : St P :=
  { declAt := P.decls.foldl (fun m (o, d) => m.insert o d) {},
    invOps := P.ops.filterMap (·.inverse) }

end SemperCheck.Replay

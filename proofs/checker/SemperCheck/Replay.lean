import SemperCheck.Parse
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
  deriving Inhabited

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
  defs : Array (Option Def) := #[]
  parent : Array Nat := #[]
  /-- `(f, c1 .. ck) -> id`: the program term `f(c1 .. ck)` evaluated to `id`. -/
  spell : Spell := {}
  /-- The node of each operator's unit (`z` lines). -/
  units : Std.HashMap String Nat := {}
  /-- Each literal's node, checked against its definition on use. -/
  lits : Std.HashMap (String × String) Nat := {}
  snaps : Array (Array Nat × Spell) := #[]
  /-- Splice witnesses for the next `t`, `c` or `w` line. -/
  splices : List (Nat × Nat) := []
  /-- The open firing: its command's offset, and whether it is a `rewrite`. -/
  fire : Option (Nat × Bool) := none
  atoms : Array (Nat × String × List Nat) := #[]
  /-- The right-hand side's nodes; `true` marks a `let` name's node. -/
  rhs : List (Nat × Bool) := []
  proved : List Nat := []
  events : Nat := 0
  failed : Std.HashMap String Nat := {}
  nFailed : Nat := 0
  /-- Measurement only: apply the merges of `u` lines without a check, to
  tell a check that fails by itself from one that fails because an earlier
  merge was not applied. A goal proved this way is not proved. -/
  assume : Bool := false
  unchecked : Std.HashMap String Nat := {}

namespace St

def fd (S : St) (i : Nat) : Nat := find S.parent i

def defOf (S : St) (i : Nat) : Option Def := S.defs.getD i none

def fail (S : St) (cause : String) : St :=
  { S with failed := S.failed.insert cause (S.failed.getD cause 0 + 1), nFailed := S.nFailed + 1,
           splices := [] }

def merge (S : St) (a b : Nat) : St :=
  { S with parent := union S.parent a b, splices := [] }

end St

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
argument in that node's class. -/
def cancelInverse (S : St) (inv : String) (xs : List Nat) : List Nat := Id.run do
  let mut out := xs.toArray
  for a in xs do
    if let some (.app g [y]) := S.defOf a then
      if g == inv then
        if let some i := out.findIdx? (· == a) then
          let rest := out.eraseIdxIfInBounds i
          if let some j := rest.findIdx? (fun b => S.fd b == S.fd y) then
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
def nf2 (S : St) (f : String) (as bs : List Nat) : List Nat × List Nat :=
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
    let u := (S.units[f]?).map S.fd
    let d := S.P.opDecl? f
    let one (xs : List Nat) : List Nat :=
      let atoms := xs.flatMap (expand S W)
      let atoms := match k, d.bind (·.inverse) with
        | .assoc, _ => atoms
        | _, some inv => cancelInverse S inv atoms
        | _, none => atoms
      let cls := (atoms.map S.fd).filter fun c => some c != u
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
`n`. -/
def spells (S : St) (n : Nat) (f : String) (cs : List Nat) : Bool :=
  (match S.defOf n with
    | some (.app g ds) => g == f && (let (x, y) := nf2 S f ds cs; x == y)
    | _ => false)
  || ((S.P.kind f).isAssoc && (nf2 S f cs []).1 == [S.fd n])

/-- Node `n`'s definition is the term `t`, argument for argument. -/
partial def denotes (S : St) (n : Nat) : Term → Bool
  | .lit s v => match S.defOf n with
    | some (.lit s' v') => s' == s && v' == v
    | _ => false
  | .app f ts => match S.defOf n with
    | some (.app g cs) => g == f && cs.length == ts.length && (cs.zip ts).all fun (c, t) => denotes S c t
    | _ => false

/-- `c` and `c:k` fields as node ids, a counted one repeated. -/
def ids (xs : List String) : Option (List Nat) := do
  let mut out : Array Nat := #[]
  for x in xs do
    match x.splitOn ":" with
    | [n] => out := out.push (← n.toNat?)
    | [n, k] =>
      let n ← n.toNat?
      let k ← k.toNat?
      if k > 65536 then none
      for _ in [0:k] do out := out.push n
    | _ => none
  return out.toList

/-! ## A rule firing -/

structure Walk where
  σ : List (String × Nat) := []
  atoms : List (Nat × String × List Nat)
  rhs : List (Nat × Bool)
  /-- The node of each matched pattern, by the pattern's printed form. -/
  memo : List (String × Nat) := []

abbrev WalkM := StateT Walk (Except String)

def key (p : Pat) : String := toString (repr p)

partial def Pat.toTerm? : Pat → Option Term
  | .var _ => none
  | .lit s v => some (.lit s v)
  | .app f ps => (ps.mapM Pat.toTerm?).map (.app f)

/-- The node the pattern `p` matched, consuming the firing's `e` lines:
arguments first, then the application's own line. -/
partial def walkQ (S : St) (p : Pat) : WalkM Nat := do
  match p with
  | .var x =>
    match (← get).σ.lookup x with
    | some n => pure n
    | none => throw "rule: unbound variable"
  | .lit s v =>
    let w ← get
    match w.atoms with
    | (n, "#lit", _) :: rest =>
      match S.defOf n with
      | some (.lit s' v') =>
        if s' == s && v' == v then set { w with atoms := rest }; pure n
        else throw "rule: literal differs"
      | _ => throw "rule: literal differs"
    | _ => throw "rule: no line for a literal"
  | .app f ps =>
    -- A ground argument the next line does not match is a `let` name's term:
    -- the engine bound it to the name's node and wrote no line for it.
    let groundNode (q : Pat) : WalkM (Option Nat) := do
      match q, (← get).atoms with
      | .app g qs, (_, h, cs) :: _ =>
        if g == h && cs.length == qs.length then pure none
        else pure ((Pat.toTerm? q).bind (eval S))
      | .app _ _, [] => pure ((Pat.toTerm? q).bind (eval S))
      | _, _ => pure none
    let mut sub : Array (Option Nat) := #[]
    for q in ps do
      match q with
      | .var _ => sub := sub.push none
      | _ =>
        match ← groundNode q with
        | some n => sub := sub.push (some n)
        | none => sub := sub.push (some (← walkQ S q))
    let w ← get
    match w.atoms with
    | (n, g, cs) :: rest =>
      if g != f || cs.length != ps.length then throw "rule: line for another application"
      let mut σ := w.σ
      for (q, o, c) in ps.zip (sub.toList.zip cs) do
        match q, o with
        | .var x, _ =>
          match σ.lookup x with
          | some y => if S.fd y != S.fd c then throw "rule: variable bound twice"
          | none => σ := (x, c) :: σ
        | _, some id => if S.fd id != S.fd c then throw "rule: argument differs"
        | _, none => throw "rule: argument differs"
      match S.defOf n with
      | some (.app h ds) =>
        if h != f || (let (x, y) := nf2 S f ds cs; x != y) then throw "rule: matched node differs"
      | _ => throw "rule: matched node differs"
      set { w with atoms := rest, σ := σ, memo := (key p, n) :: w.memo }
      pure n
    | [] => throw "rule: no line for an application"

/-- The node the pattern `p` was built as, consuming the firing's `b` nodes. -/
partial def walkB (S : St) (p : Pat) : WalkM Nat := do
  match p with
  | .var x =>
    match (← get).σ.lookup x with
    | some n => pure n
    | none => throw "rule: unbound variable"
  | _ =>
    let w ← get
    -- A `let` name's term: the engine fetched the name's node.
    if let (n, true) :: rest := w.rhs then
      match (Pat.toTerm? p).bind (eval S) with
      | some m =>
        if S.fd m == S.fd n then set { w with rhs := rest }; return n
        else throw "rule: let name differs"
      | none => throw "rule: let name differs"
    match p with
    | .lit s v =>
      match w.rhs with
      | (n, _) :: rest =>
        match S.defOf n with
        | some (.lit s' v') =>
          if s' == s && v' == v then set { w with rhs := rest }; pure n
          else throw "rule: built literal differs"
        | _ => throw "rule: built literal differs"
      | [] => throw "rule: no node for a built literal"
    | .app f ps =>
      let cs ← ps.mapM (walkB S)
      let w ← get
      match w.rhs with
      | (n, _) :: rest =>
        if spells S n f cs then set { w with rhs := rest }; pure n
        else throw "rule: built node differs"
      | [] => throw "rule: no node for a built application"
    | .var _ => throw "rule: unbound variable"

/-- One side of a body equality: a bound variable's node, a matched pattern's
node, or `none` for a variable not bound yet. -/
def side (S : St) (p : Pat) : WalkM (Option Nat) := do
  match p with
  | .var x => pure ((← get).σ.lookup x)
  | _ =>
    match (← get).memo.lookup (key p) with
    | some n => pure (some n)
    | none => some <$> walkQ S p

def bindVar (p : Pat) (n : Nat) : WalkM Unit := do
  match p with
  | .var x => modify fun w => { w with σ := (x, n) :: w.σ }
  | _ => throw "rule: equality without a node"

def nodeSort (S : St) (n : Nat) : Option String :=
  match S.defOf n with
  | some (.lit s _) => some s
  | some (.app f _) => (S.P.opDecl? f).map (·.res)
  | none => none

/-- The nodes of the two sides of rule `r`, instantiated by the firing. -/
def fireRule (S : St) (r : Rule) (rewrite : Bool) : WalkM (Nat × Nat) := do
  let nl? ← if rewrite then some <$> walkQ S r.lhs else pure none
  for (p, q) in r.eqs do
    match ← side S p, ← side S q with
    | some a, some b => if S.fd a != S.fd b then throw "rule: body equality does not hold"
    | none, some b => bindVar p b
    | some a, none => bindVar q a
    | none, none => throw "rule: equality without a node"
  let nl ← match nl? with
    | some n => pure n
    | none => walkB S r.lhs
  let nr ← walkB S r.rhs
  let w ← get
  for x in r.vars do
    match w.σ.lookup x, r.sorts.lookup x with
    | some n, some s => if nodeSort S n != some s then throw "rule: variable of another sort"
    | _, _ => throw "rule: unbound variable"
  pure (nl, nr)

/-! ## One line -/

def setDef (S : St) (i : Nat) (d : Def) : St :=
  let defs := if S.defs.size ≤ i then S.defs ++ Array.replicate (i + 1 - S.defs.size) none
    else S.defs
  { S with defs := defs.setIfInBounds i (some d) }

def step (S : St) (line : String) : St :=
  let S := { S with events := S.events + 1 }
  match line.splitOn " " with
  | "n" :: id :: f :: kids =>
    match id.toNat?, ids kids with
    | some i, some cs =>
      if cs.all (· < i) then setDef S i (.app f cs) else S.fail "definition: argument after its node"
    | _, _ => S.fail "definition: unreadable"
  | "l" :: id :: s :: rest =>
    match id.toNat? with
    | some i =>
      let v := " ".intercalate rest
      let S := setDef S i (.lit s v)
      { S with lits := S.lits.insert (s, v) i }
    | none => S.fail "definition: unreadable"
  | "t" :: id :: f :: kids =>
    match id.toNat?, ids kids with
    | some i, some cs =>
      if spells S i f cs then { S with spell := S.spell.insert (f, cs) i, splices := [] }
      else S.fail "term: its node differs"
    | _, _ => S.fail "term: unreadable"
  | ["s", c, m] =>
    match c.toNat?, m.toNat? with
    | some c, some m => { S with splices := (c, m) :: S.splices, events := S.events - 1 }
    | _, _ => S.fail "splice: unreadable"
  | ["z", f, u] =>
    match u.toNat?, (S.P.opDecl? f).bind (·.unit) with
    | some u, some t =>
      if denotes S u t then { S with units := S.units.insert f u, events := S.events - 1 }
      else S.fail "unit: its node differs"
    | _, _ => S.fail "unit: no such unit"
  | ["x", off, a, b] =>
    match off.toNat?, a.toNat?, b.toNat? with
    | some o, some a, some b =>
      match S.declAt[o]? with
      | some (.axiom l r) =>
        if eval S l == some a && eval S r == some b then S.merge a b
        else S.fail "union: its terms differ"
      | _ => S.fail "union: no such command"
    | _, _, _ => S.fail "union: unreadable"
  | ["c", a, b] =>
    match a.toNat?, b.toNat? with
    | some a, some b =>
      match S.defOf a, S.defOf b with
      | some (.app f as), some (.app g bs) =>
        if f == g && (let (x, y) := nf2 S f as bs; x == y) then S.merge a b
        else S.fail "congruence: arguments differ"
      | _, _ => S.fail "congruence: not two applications"
    | _, _ => S.fail "congruence: unreadable"
  | ["w", a, b] =>
    match a.toNat?, b.toNat? with
    | some a, some b =>
      match S.defOf a with
      | some (.app f as) => if spells S b f as then S.merge a b else S.fail "law: arguments differ"
      | _ => S.fail "law: not an application"
    | _, _ => S.fail "law: unreadable"
  | ["r", off, kind] =>
    match off.toNat? with
    | some o => { S with fire := some (o, kind == "w"), atoms := #[], rhs := [], events := S.events - 1 }
    | none => S.fail "rule: unreadable"
  | "e" :: id :: f :: kids =>
    match id.toNat?, ids kids with
    | some i, some cs => { S with atoms := S.atoms.push (i, f, cs), events := S.events - 1 }
    | _, _ => S.fail "rule: unreadable"
  | "b" :: xs =>
    let one (x : String) : Option (Nat × Bool) :=
      if x.startsWith "g" then (x.drop 1).toString.toNat?.map (·, true) else x.toNat?.map (·, false)
    match xs.mapM one with
    | some r => { S with rhs := r, events := S.events - 1 }
    | none => S.fail "rule: unreadable"
  | ["m", j, a, b] =>
    match j.toNat?, a.toNat?, b.toNat?, S.fire with
    | some j, some a, some b, some (o, rw) =>
      -- The engine cites a rule by an offset inside its command.
      match ((S.P.decls.filter (·.1 ≤ o)).getLast?.map (·.2) : Option Decl) with
      | some (Decl.rules rs) =>
        match rs[j]? with
        | some (some r) =>
          match (fireRule S r rw).run { atoms := S.atoms.toList, rhs := S.rhs } with
          | .ok ((nl, nr), _) =>
            if (S.fd nl == S.fd a && S.fd nr == S.fd b) || (S.fd nl == S.fd b && S.fd nr == S.fd a)
            then S.merge a b
            else S.fail "rule: merged nodes differ"
          | .error e => S.fail e
        | _ => S.fail "rule: outside the reader's language"
      | _ => S.fail "rule: no such command"
    | _, _, _, _ => S.fail "rule: unreadable"
  | ["g", off, a, b] =>
    match off.toNat?, a.toNat?, b.toNat? with
    | some o, some a, some b =>
      match S.declAt[o]? with
      | some (.goal l r) =>
        if eval S l == some a && eval S r == some b then
          if S.fd a == S.fd b then { S with proved := o :: S.proved }
          else S.fail "goal: not in one class"
        else S.fail "goal: its terms differ"
      | _ => S.fail "goal: no such command"
    | _, _, _ => S.fail "goal: unreadable"
  | ["mark", d] =>
    match d.toNat? with
    | some (d + 1) => { S with snaps := (S.snaps.extract 0 d).push (S.parent, S.spell) }
    | _ => S.fail "mark: unreadable"
  | ["restore", d] =>
    match d.toNat? with
    | some (d + 1) =>
      match S.snaps[d]? with
      | some (p, sp) => { S with parent := p, spell := sp, snaps := S.snaps.extract 0 (d + 1), fire := none }
      | none => S.fail "restore: no such mark"
    | _ => S.fail "restore: unreadable"
  | ["rpop", d] =>
    match d.toNat? with
    | some d =>
      match S.snaps[d]? with
      | some (p, sp) => { S with parent := p, spell := sp, snaps := S.snaps.extract 0 d, fire := none }
      | none => S.fail "restore: no such mark"
    | none => S.fail "restore: unreadable"
  | "u" :: kind :: rest =>
    let S := { S with unchecked := S.unchecked.insert kind (S.unchecked.getD kind 0 + 1), splices := [] }
    match S.assume, rest with
    | true, [a, b] =>
      match a.toNat?, b.toNat? with
      | some a, some b => S.merge a b
      | _, _ => S
    | _, _ => S
  | [""] => { S with events := S.events - 1 }
  | _ => S.fail "unreadable line"

def start (P : Program) : St :=
  { P, declAt := P.decls.foldl (fun m (o, d) => m.insert o d) {} }

end SemperCheck.Replay

import SemperCheck.Syntax
import Std.Data.HashMap

/-!
# The certificate and its checker

A certificate is a table of nodes and a list of steps. Node `i` is a literal
or an operator applied to nodes before `i`, so it denotes one ground term.
Each step concludes an equality `a = b` between two nodes, from earlier steps
and the program, by one of six inferences:

* `refl a`: `a = a`.
* `symm s`, `trans s t`: from the conclusions of steps `s` and `t`.
* `axiom o a b`: the `union` at offset `o` states `a = b`.
* `rule o j σ prems a b`: rule `j` of the command at offset `o`, instantiated
  by `σ`, has `a` as its left side and `b` as its right side, and step
  `prems[k]` proves its `k`-th equality premise.
* `cong f a b prems`: `a` and `b` are equal modulo the laws of `f` once the
  premises' left nodes are replaced by their right nodes: as two applications
  of `f` whose children are pairwise equal or a premise (every operator), as
  two applications of a `comm` operator with swapped children, or, for an
  `assoc`, `ac` or `aci` operator, as the sequences of arguments each side
  flattens to, with the premises applied to each argument and the result
  flattened again, the unit removed, and the two sequences compared as lists
  (`assoc`), as multisets (`ac`) or as sets (`aci`).

A conclusion also records the offset before which every command it cites
starts, so a `check-eq` can use only the commands before it.

Every node has a sort (`nodeSort`): a literal's is the one it carries, an
application's is its operator's result sort. The table is well-sorted
(`wfSorts`): each child has the sort its position takes, and each literal is
of a literal sort. A step concludes only an equality between two nodes of one
sort, a rule is instantiated only with nodes of its variables' sorts, and the
congruence of an associative operator compares only nodes of its sort.
-/

namespace SemperCheck

inductive Node where
  | lit (s v : String)
  | app (f : String) (cs : List Nat)
  deriving Repr, DecidableEq, Hashable, Inhabited

inductive Step where
  | refl (a : Nat)
  | symm (s : Nat)
  | trans (s t : Nat)
  | axiom (o a b : Nat)
  | rule (o j : Nat) (σ : List (String × Nat)) (prems : List Nat) (a b : Nat)
  | cong (f : String) (a b : Nat) (prems : List Nat)
  deriving Repr, Inhabited

structure Cert where
  nodes : Array Node
  steps : Array Step
  /-- `(o, s)`: step `s` proves the `check-eq` at offset `o`. -/
  goals : List (Nat × Nat)
  deriving Repr, Inhabited

/-- `a = b`, citing only commands that start before `pos`. -/
structure Concl where
  a : Nat
  b : Nat
  pos : Nat
  deriving Repr, Inhabited

/-- Every child of node `i` is a node before `i`. -/
def wfNodes (nodes : Array Node) : Bool :=
  (List.range nodes.size).all fun i =>
    match nodes[i]? with
    | some (.app _ cs) => cs.all (· < i)
    | _ => true

/-- The sort of node `i`. -/
def nodeSort (P : Program) (nodes : Array Node) (i : Nat) : Option String :=
  match nodes[i]? with
  | some (.lit s _) => some s
  | some (.app f _) => (P.opDecl? f).map (·.res)
  | none => none

/-- Each child is a node of the sort at its position. -/
def argsOk (P : Program) (nodes : Array Node) : List String → List Nat → Bool
  | [], [] => true
  | s :: ss, c :: cs => nodeSort P nodes c == some s && argsOk P nodes ss cs
  | _, _ => false

/-- Every node is well-sorted: a literal is of a literal sort; an application
is of a declared operator, with children of its argument sorts, and an
application of an `assoc`, `ac` or `aci` operator with no children has a
unit. -/
def wfSorts (P : Program) (nodes : Array Node) : Bool :=
  (List.range nodes.size).all fun i =>
    match nodes[i]? with
    | some (.lit s _) => P.litSorts.contains s
    | some (.app f cs) =>
      match P.opDecl? f with
      | none => false
      | some d =>
        if d.kind.isAssoc then
          cs.all (fun c => nodeSort P nodes c == some d.res) && (!cs.isEmpty || d.unit.isSome)
        else argsOk P nodes d.args cs
    | none => true

structure Ctx where
  P : Program
  nodes : Array Node
  index : Std.HashMap Node Nat

namespace Ctx

variable (C : Ctx)

def sortOf (i : Nat) : Option String := nodeSort C.P C.nodes i

/-- The node `n`, found through the index and confirmed in the table. -/
def lookup (n : Node) : Option Nat :=
  match C.index[n]? with
  | some i => if C.nodes[i]? = some n then some i else none
  | none => none

/-- The node that is term `t`, child for child. -/
def intern : Term → Option Nat
  | .lit s v => C.lookup (.lit s v)
  | .app f args => (args.mapM intern).bind fun ids => C.lookup (.app f ids)

/-- The node that is pattern `p` with each variable read from `σ`. -/
def instP (σ : List (String × Nat)) : Pat → Option Nat
  | .var x => σ.lookup x
  | .lit s v => C.lookup (.lit s v)
  | .app f ps => (ps.mapM (instP σ)).bind fun ids => C.lookup (.app f ids)

/-- The arguments node `x` flattens to under `f`: the arguments of each
application of `f`, recursively, and `[x]` for any other node. An application
of `f` with no arguments has no view. -/
def view (f : String) (x : Nat) : Option (List Nat) :=
  match C.nodes[x]? with
  | some (.app g cs) =>
    if g = f then
      if cs.isEmpty then none
      else (cs.mapM fun c => if _h : c < x then view f c else none).map List.flatten
    else some [x]
  | _ => some [x]
termination_by x

end Ctx

/-- The right node of the first premise whose left node is `y`, else `y`. -/
def substOf (prems : List (Nat × Nat)) (y : Nat) : Nat :=
  match prems.find? (·.1 == y) with
  | some p => p.2
  | none => y

def dropUnit : Option Nat → List Nat → List Nat
  | none, l => l
  | some u, l => l.filter (· != u)

namespace Ctx

variable (C : Ctx)

/-- The node of the unit of `f`, if it has one and the table holds it. -/
def unitOf (f : String) : Option Nat :=
  match C.P.opDecl? f with
  | some d => d.unit.bind C.intern
  | none => none

/-- The arguments `x` flattens to under `f`, each replaced by its premise and
flattened again, with the unit removed. -/
def side (f : String) (prems : List (Nat × Nat)) (x : Nat) : Option (List Nat) :=
  match C.view f x with
  | none => none
  | some v =>
    match v.mapM (fun y => C.view f (substOf prems y)) with
    | none => none
    | some ws => some (dropUnit (C.unitOf f) ws.flatten)

end Ctx

def sameBy : Kind → List Nat → List Nat → Bool
  | .assoc, l, m => l == m
  | .ac, l, m => l.isPerm m
  | .aci, l, m => l.all (· ∈ m) && m.all (· ∈ l)
  | _, _, _ => false

/-- Children pairwise equal or a premise. -/
def pairsOk (prems : List (Nat × Nat)) : List Nat → List Nat → Bool
  | [], [] => true
  | c :: cs, d :: ds => (c == d || prems.contains (c, d)) && pairsOk prems cs ds
  | _, _ => false

namespace Ctx

variable (C : Ctx)

def congPlain (f : String) (a b : Nat) (prems : List (Nat × Nat)) : Bool :=
  match C.nodes[a]?, C.nodes[b]? with
  | some (.app g cs), some (.app h ds) => g == f && h == f && pairsOk prems cs ds
  | _, _ => false

def congComm (f : String) (a b : Nat) (prems : List (Nat × Nat)) : Bool :=
  match C.nodes[a]?, C.nodes[b]? with
  | some (.app g [c1, c2]), some (.app h [d1, d2]) =>
    g == f && h == f && pairsOk prems [c1, c2] [d2, d1]
  | _, _ => false

def congAssoc (f : String) (a b : Nat) (prems : List (Nat × Nat)) : Bool :=
  match C.P.opDecl? f, C.side f prems a, C.side f prems b with
  | some d, some l, some m =>
    C.sortOf a == some d.res && C.sortOf b == some d.res && sameBy d.kind l m
  | _, _, _ => false

def congOk (f : String) (a b : Nat) (prems : List (Nat × Nat)) : Bool :=
  C.congPlain f a b prems ||
    match C.P.kind f with
    | .plain => false
    | .comm => C.congComm f a b prems
    | _ => C.congAssoc f a b prems

/-- The command at offset `o`. -/
def decl? (o : Nat) : Option Decl :=
  (C.P.decls.find? (·.1 == o)).map (·.2)

def eqsOk (σ : List (String × Nat)) : List (Pat × Pat) → List (Nat × Nat) → Bool
  | [], [] => true
  | (p, q) :: es, (x, y) :: ps =>
    C.instP σ p == some x && C.instP σ q == some y && eqsOk σ es ps
  | _, _ => false

/-- Each variable of the rule is bound by `σ` to a node of its sort. -/
def sortsOk (σ : List (String × Nat)) (r : Rule) : Bool :=
  r.vars.all fun x =>
    match σ.lookup x, r.sorts.lookup x with
    | some n, some s => C.sortOf n == some s
    | _, _ => false

end Ctx

/-- The premises' equalities and the largest of their offsets. -/
def premConcls (acc : Array Concl) (prems : List Nat) : Option (List (Nat × Nat) × Nat) :=
  (prems.mapM fun s => acc[s]?).map fun cs => (cs.map fun c => (c.a, c.b), cs.foldl (fun m c => max m c.pos) 0)

namespace Ctx

variable (C : Ctx)

def inferStep (acc : Array Concl) : Step → Option Concl
  | .refl a => some ⟨a, a, 0⟩
  | .symm s => acc[s]?.map fun c => ⟨c.b, c.a, c.pos⟩
  | .trans s t =>
    match acc[s]?, acc[t]? with
    | some c, some d => if c.b = d.a then some ⟨c.a, d.b, max c.pos d.pos⟩ else none
    | _, _ => none
  | .axiom o a b =>
    match C.decl? o with
    | some (.axiom l r) =>
      if C.intern l = some a ∧ C.intern r = some b then some ⟨a, b, o + 1⟩ else none
    | _ => none
  | .rule o j σ prems a b =>
    match C.decl? o with
    | some (.rules rs) =>
      match rs[j]?, premConcls acc prems with
      | some (some r), some (ps, pos) =>
        if C.instP σ r.lhs = some a ∧ C.instP σ r.rhs = some b ∧ C.eqsOk σ r.eqs ps = true ∧
            C.sortsOk σ r = true then
          some ⟨a, b, max (o + 1) pos⟩
        else none
      | _, _ => none
    | _ => none
  | .cong f a b prems =>
    match premConcls acc prems with
    | some (ps, pos) => if C.congOk f a b ps then some ⟨a, b, pos⟩ else none
    | none => none

/-- The conclusion of a step that does not check: `0 = 0`, which holds, so a
step citing it concludes only what it would from a reflexivity. A writer's
mistake then leaves the goals that depend on it unproved instead of
rejecting the certificate. -/
def failed : Concl := ⟨0, 0, 0⟩

/-- A step's conclusion, if the step checks and its two nodes are of one
sort. -/
def checkStep (acc : Array Concl) (st : Step) : Option Concl :=
  match C.inferStep acc st with
  | some c => if C.sortOf c.a = C.sortOf c.b ∧ (C.sortOf c.a).isSome then some c else none
  | none => none

def checkSteps : List Step → Array Concl → Option (Array Concl)
  | [], acc => some acc
  | s :: ss, acc => checkSteps ss (acc.push ((C.checkStep acc s).getD failed))

/-- Step `s` of the certificate proves `l = r` citing only commands before `o`. -/
def checkGoal (acc : Array Concl) (goals : List (Nat × Nat)) (o : Nat) (l r : Term) : Bool :=
  match goals.find? (·.1 == o) with
  | some (_, s) =>
    match acc[s]?, C.intern l, C.intern r with
    | some c, some a, some b => c.a == a && c.b == b && decide (c.pos ≤ o)
    | _, _, _ => false
  | none => false

end Ctx

def mkCtx (P : Program) (cert : Cert) : Ctx :=
  { P, nodes := cert.nodes,
    index := cert.nodes.toList.zipIdx.foldl (fun m (n, i) => m.insert n i) {} }

/-- The conclusions of every step, if every step checks. -/
def runCert (P : Program) (cert : Cert) : Option (Ctx × Array Concl) :=
  if wfNodes cert.nodes && wfSorts P cert.nodes then
    let C := mkCtx P cert
    (C.checkSteps cert.steps.toList #[]).map (C, ·)
  else none

end SemperCheck

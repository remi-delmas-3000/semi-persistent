import SemperCheck.Syntax
import SemperCheck.Prim

/-!
# What a sequence rule yields under a binding

`seqApply r B` is the pair of terms rule `r` equates under the binding `B`:
the left side is the root operator applied to its items (a rest sequence
gives its atoms, a filter gives one instance of its pattern per element, as
many times as the element's count), or the rule's left pattern under the
binding; the right side is built from the same elements. It is part of the
statement of the soundness theorem: a model satisfies `r` when the two terms
are equal under every binding and every valuation of the atoms
(`Semantics.lean`, `SeqSat`).

A binding names what one firing collected. The statement does not ask that
the filter's elements be all the arguments that match its pattern.
-/

namespace SemperCheck

/-- The count `n` as a value of sort `sort`. -/
def natVal (sort : String) (n : Nat) : Option Val :=
  match sort with
  | "i64" => Val.ofI64 n
  | "u64" => if n < Val.two64 then some (.u64 n) else none
  | "usize" => if n < Val.two64 then some (.usize n) else none
  | "IBig" => some (.ibig n)
  | "UBig" => some (.ubig n)
  | _ => none

/-- A value as a count. -/
def Val.toNat? : Val → Option Nat
  | .i64 v => if 0 ≤ v then some v.toNat else none
  | .ibig v => if 0 ≤ v then some v.toNat else none
  | .u64 v => some v
  | .usize v => some v
  | .ubig v => some v
  | _ => none

mutual

/-- Pattern `p` under the binding `B`, each variable read by `look`. -/
def patB (B : SBind) (look : String → Option SAtom) : Pat → Option STm
  | .var x => (look x).map .atom
  | .lit s v => some (.atom (.lit s v))
  | .app f ps => (patsB B look ps).map (.app f)
  | .count k => (B.kcounts.lookup k).map fun n => .atom (.lit "i64" (toString n))
  | .rest _ => none
  | .rep _ _ => none
  | .times _ _ => none

/-- An argument list: a rest variable gives its atoms, a counted argument its
instance as many times as its count. -/
def patsB (B : SBind) (look : String → Option SAtom) : List Pat → Option (List STm)
  | [] => some []
  | .rest x :: ps =>
    (B.seqs.lookup x).bind fun xs => (patsB B look ps).map (xs.map .atom ++ ·)
  | .rep p k :: ps =>
    (B.kcounts.lookup k).bind fun n => (patB B look p).bind fun t =>
      (patsB B look ps).map (List.replicate n t ++ ·)
  | .times p n :: ps =>
    (patB B look p).bind fun t => (patsB B look ps).map (List.replicate n t ++ ·)
  | .var x :: ps => (look x).bind fun a => (patsB B look ps).map (.atom a :: ·)
  | .lit s v :: ps => (patsB B look ps).map (.atom (.lit s v) :: ·)
  | .count k :: ps =>
    (B.kcounts.lookup k).bind fun n =>
      (patsB B look ps).map (.atom (.lit "i64" (toString n)) :: ·)
  | .app f qs :: ps =>
    (patsB B look qs).bind fun as => (patsB B look ps).map (.app f as :: ·)

end

namespace SBind

/-- The value of variable `x` at element `i` of a filter: its column's entry,
or the scalar. -/
def look (B : SBind) (i : Option Nat) (x : String) : Option SAtom :=
  match i.bind fun i => (B.cols.lookup x).bind (·[i]?) with
  | some a => some a
  | none => B.scalars.lookup x

/-- The instance of pattern `p` at each element, with the element's count,
from element `i` on. -/
def rowsFrom (B : SBind) (p : Pat) (i : Nat) : List Nat → Option (List (STm × Nat))
  | [] => some []
  | k :: ks =>
    (patB B (B.look (some i)) p).bind fun t => (rowsFrom B p (i + 1) ks).map ((t, k) :: ·)

end SBind

/-- Equal neighbours as one entry with their number. -/
def groupsOf : List SAtom → List (SAtom × Nat)
  | [] => []
  | a :: as =>
    match groupsOf as with
    | (b, k) :: r => if a == b then (b, k + 1) :: r else (a, 1) :: (b, k) :: r
    | [] => [(a, 1)]

/-- The rows of the sequence named `x`, each with its count: the elements of
the filter `x`; else the column `x`; else the rest sequence `x`, its equal
neighbours as one row when `grouped`. -/
def srcRows (r : SeqRule) (B : SBind) (grouped : Bool) (x : String) : Option (List (STm × Nat)) :=
  match r.items.findSome? (fun it => match it with
      | .filter g p => if g == x then some p else none
      | _ => none) with
  | some p => (B.counts.lookup x).bind (B.rowsFrom p 0)
  | none =>
    match B.cols.lookup x with
    | some as => some (as.map fun a => (.atom a, 1))
    | none =>
      (B.seqs.lookup x).map fun as =>
        if grouped then (groupsOf as).map fun (a, k) => (.atom a, k)
        else as.map fun a => (.atom a, 1)

/-- The rows a comprehension ranges over: each the values of its binders and
a count. Side by side, the rows stop at the shortest sequence and take the
first one's counts. -/
def rowsOf (r : SeqRule) (B : SBind) (grouped : Bool) : SSrc → Option (List (List STm × Nat))
  | .one x => (srcRows r B grouped x).map (·.map fun (t, k) => ([t], k))
  | .concat xs =>
    (xs.mapM (srcRows r B grouped)).map fun ls => ls.flatten.map fun (t, k) => ([t], k)
  | .zip xs =>
    (xs.mapM (srcRows r B grouped)).map fun ls =>
      let n := (ls.map (·.length)).foldl min ((ls.head?.map (·.length)).getD 0)
      (List.range n).map fun i =>
        (ls.filterMap fun l => (l[i]?).map (·.1), ((ls.head?.bind (·[i]?)).map (·.2)).getD 1)

/-- The arguments a left-side item stands for. -/
def SItem.args (B : SBind) : SItem → Option (List STm)
  | .rest x => (B.seqs.lookup x).map (·.map .atom)
  | .filter g p =>
    ((B.counts.lookup g).bind (B.rowsFrom p 0)).map fun rows =>
      rows.flatMap fun (t, k) => List.replicate k t
  | .one p => (patB B (B.look none) p).map ([·])

def itemsArgs (B : SBind) : List SItem → Option (List STm)
  | [] => some []
  | it :: its => (it.args B).bind fun a => (itemsArgs B its).map (a ++ ·)

/-- What `..x` splices: the elements of the filter named `x`, else the rest
sequence `x`. -/
def spliceOf (r : SeqRule) (B : SBind) (x : String) : Option (List STm) :=
  match r.items.find? (fun it => match it with | .filter g _ => g == x | _ => false) with
  | some it => it.args B
  | none => (B.seqs.lookup x).map (·.map .atom)

/-- What a comprehension binds while its body is built. -/
structure SLoc where
  vals : List (String × STm) := []
  cnts : List (String × Nat) := []

mutual

/-- The value of `e` under the binding: a filter's count is the number of its
elements, as an `i64`. -/
def numS (B : SBind) (lc : SLoc) : SNum → Option Val
  | .lit s v => Val.parse s v
  | .var x =>
    match lc.vals.lookup x with
    | some (.atom (.lit s v)) => Val.parse s v
    | some _ => none
    | none =>
      match B.scalars.lookup x with
      | some (.lit s v) => Val.parse s v
      | _ => none
  | .count g => (B.counts.lookup g).map fun ks => .i64 ks.length
  | .sum g => (B.counts.lookup g).map fun ks => .i64 ((ks.foldl (· + ·) 0 : Nat) : Int)
  | .cnt x s =>
    match lc.cnts.lookup x with
    | some n => natVal s n
    | none => (B.kcounts.lookup x).bind (natVal s)
  | .prim f args => (numsS B lc args).bind (primEval f)

def numsS (B : SBind) (lc : SLoc) : List SNum → Option (List Val)
  | [] => some []
  | e :: es => (numS B lc e).bind fun v => (numsS B lc es).map (v :: ·)

end

/-- Whether the condition `g`, when there is one, computes `true`. -/
def holdsS (B : SBind) (lc : SLoc) : Option SNum → Option Bool
  | none => some true
  | some g =>
    match numS B lc g with
    | some (.bool b) => some b
    | _ => none

/-- The count `k` computes, 1 without it. -/
def timesS (B : SBind) (lc : SLoc) : Option SNum → Option Nat
  | none => some 1
  | some k => (numS B lc k).bind Val.toNat?

mutual

def rhsS (r : SeqRule) (B : SBind) (lc : SLoc) : SRhs → Option STm
  | .val e => (numS B lc e).bind fun v => v.spell.map fun t => .atom (.lit v.sortName t)
  | .var x =>
    match lc.vals.lookup x with
    | some t => some t
    | none => (B.scalars.lookup x).map .atom
  | .lit s v => some (.atom (.lit s v))
  | .app f args => (argsS r B lc args).map (.app f)

def argsS (r : SeqRule) (B : SBind) (lc : SLoc) : List SArg → Option (List STm)
  | [] => some []
  | .tm t :: as => (rhsS r B lc t).bind fun x => (argsS r B lc as).map (x :: ·)
  | .splice x :: as => (spliceOf r B x).bind fun xs => (argsS r B lc as).map (xs ++ ·)
  | .times t k :: as =>
    (timesS B lc (some k)).bind fun n => (rhsS r B lc t).bind fun x =>
      (argsS r B lc as).map (List.replicate n x ++ ·)
  | .comp body bs kv src grouped guard mult :: as =>
    (rowsOf r B grouped src).bind fun rows =>
      (rows.zipIdx.mapM fun ((row, i) : (List STm × Nat) × Nat) =>
        -- Row `i` also reads each filter variable at element `i`.
        let cols : List (String × STm) := B.cols.filterMap fun (ca : String × List SAtom) =>
          (ca.2[i]?).map fun a => (ca.1, STm.atom a)
        let lc' : SLoc := { vals := bs.zip row.1 ++ cols ++ lc.vals,
                            cnts := (match kv with | some x => [(x, row.2)] | none => []) ++ lc.cnts }
        (holdsS B lc' guard).bind fun ok =>
          if ok then
            (timesS B lc' mult).bind fun n => (rhsS r B lc' body).map (List.replicate n)
          else some []).bind fun parts =>
        (argsS r B lc as).map (parts.flatten ++ ·)

end

/-- The two terms rule `r` equates under binding `B`, when each of its
conditions computes `true` and each element of a counted filter has at least
the filter's least count. -/
def seqApply (r : SeqRule) (B : SBind) : Option (STm × STm) :=
  if !(r.guards.all fun g => holdsS B {} (some g) == some true) then none
  else if !(r.least.all fun (g, n) => match B.counts.lookup g with
      | some ks => ks.all (n ≤ ·)
      | none => false) then none
  else
    let L := match r.lhs with
      | some p => patB B (B.look none) p
      | none => (itemsArgs B r.items).map (.app r.op)
    L.bind fun L => (rhsS r B {} r.rhs).map fun R => (L, R)

end SemperCheck

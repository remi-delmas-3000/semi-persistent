import SemperCheck.Syntax
import SemperCheck.Prim

/-!
# What a sequence rule yields under a binding

`seqApply r B` is the pair of terms rule `r` equates under the binding `B`:
the left side is the root operator applied to its items (a rest sequence
gives its atoms, a filter gives one instance of its pattern per element, with
the element's count), or the rule's left pattern under the binding; the right
side is built from the same elements. An argument that occurs `k` times is
held once with the count `k` (`STm.app`), and a row that occurs `m` times in
a row once with `m`: the evaluation costs the number of distinct neighbours,
not the counts. It is part of the
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
  | .app f ps => (patsB B look ps).map (STm.mk f)
  | .count k => (B.kcounts.lookup k).map fun n => .atom (.lit "i64" (toString n))
  | .rest _ => none
  | .rep _ _ => none
  | .times _ _ => none

/-- An argument list, each argument with its count: a rest variable gives its
atoms with theirs, a counted argument its instance with its count. -/
def patsB (B : SBind) (look : String → Option SAtom) : List Pat → Option (List (STm × Nat))
  | [] => some []
  | .rest x :: ps =>
    (B.seqs.lookup x).bind fun xs =>
      (patsB B look ps).map ((xs.map fun ak => (STm.atom ak.1, ak.2)) ++ ·)
  | .rep p k :: ps =>
    (B.kcounts.lookup k).bind fun n => (patB B look p).bind fun t =>
      (patsB B look ps).map ((t, n) :: ·)
  | .times p n :: ps =>
    (patB B look p).bind fun t => (patsB B look ps).map ((t, n) :: ·)
  | .var x :: ps => (look x).bind fun a => (patsB B look ps).map ((.atom a, 1) :: ·)
  | .lit s v :: ps => (patsB B look ps).map ((.atom (.lit s v), 1) :: ·)
  | .count k :: ps =>
    (B.kcounts.lookup k).bind fun n =>
      (patsB B look ps).map ((.atom (.lit "i64" (toString n)), 1) :: ·)
  | .app f qs :: ps =>
    (patsB B look qs).bind fun as => (patsB B look ps).map ((STm.mk f as, 1) :: ·)

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

/-- Equal neighbours as one entry, their counts added; an entry of count zero
is left out. -/
def groupsOf : List (SAtom × Nat) → List (SAtom × Nat)
  | [] => []
  | (a, j) :: as =>
    if j = 0 then groupsOf as
    else
      match groupsOf as with
      | (b, k) :: r => if a == b then (b, k + j) :: r else (a, j) :: (b, k) :: r
      | [] => [(a, j)]

/-- The rows of the sequence named `x`. A row is a value, its count, and the
number of times the row occurs in a row: the elements of the filter `x`, each
once with its count; else the column `x`; else the rest sequence `x`, whose
equal neighbours are one row with their number as its count when `grouped`,
and else one row of count 1 that occurs as many times. -/
def srcRows (r : SeqRule) (B : SBind) (grouped : Bool) (x : String) :
    Option (List (STm × Nat × Nat)) :=
  match r.items.findSome? (fun it => match it with
      | .filter g p => if g == x then some p else none
      | _ => none) with
  | some p => ((B.counts.lookup x).bind (B.rowsFrom p 0)).map (·.map fun tk => (tk.1, tk.2, 1))
  | none =>
    match B.cols.lookup x with
    | some as => some (as.map fun a => (.atom a, 1, 1))
    | none =>
      (B.seqs.lookup x).map fun as =>
        if grouped then (groupsOf as).map fun (a, k) => (.atom a, k, 1)
        else (groupsOf as).map fun (a, k) => (.atom a, 1, k)

/-- Sequences of rows side by side: each entry holds the value and count each
sequence has at a position, and the number of consecutive positions that have
them. The rows stop at the shortest sequence. `fuel` bounds the number of
entries: the number of rows of all sequences. -/
def sideRows : Nat → List (List (STm × Nat × Nat)) → List (List (STm × Nat) × Nat)
  | 0, _ => []
  | fuel + 1, ls =>
    match ls.mapM List.head? with
    | none => []
    | some hs =>
      let m := (hs.map (·.2.2)).foldl min ((hs.head?.map (·.2.2)).getD 0)
      if m = 0 then []
      else
        (hs.map fun h => (h.1, h.2.1), m) :: sideRows fuel (ls.map fun l =>
          match l with
          | (t, k, n) :: rest => if n ≤ m then rest else (t, k, n - m) :: rest
          | [] => [])

/-- `sideRows` with the fuel its sequences need. -/
def besides (ls : List (List (STm × Nat × Nat))) : List (List (STm × Nat) × Nat) :=
  sideRows ((ls.map (·.length)).foldl (· + ·) 1) ls

/-- A literal atom as an integer, with its sort. -/
def intOf : STm → Option (Int × String)
  | .atom (.lit s v) =>
    match Val.parse s v with
    | some (.i64 n) => some (n, s)
    | some (.ibig n) => some (n, s)
    | some (.u64 n) => some (n, s)
    | some (.usize n) => some (n, s)
    | some (.ubig n) => some (n, s)
    | _ => none
  | _ => none

/-- The union of integer intervals, as the engine computes it: the intervals
in order of lower then upper bound, an interval that starts at most one past
the last one's end extending it. -/
def unionInts (w : List (Int × Int)) : List (Int × Int) :=
  let before (x y : Int × Int) : Bool := x.1 < y.1 || (x.1 == y.1 && x.2 < y.2)
  let insert (sorted : List (Int × Int)) (x : Int × Int) : List (Int × Int) :=
    sorted.takeWhile (fun y => !before x y) ++ x :: sorted.dropWhile (fun y => !before x y)
  ((w.foldl insert []).foldl (fun (out : List (Int × Int)) (lu : Int × Int) =>
    match out with
    | last :: rest => if lu.1 ≤ last.2 + 1 then (last.1, max last.2 lu.2) :: rest else lu :: out
    | [] => [lu]) []).reverse

/-- The interval `[c, d]` shrunk past the windows: its start moves past a
window that covers it and ends before `d`; its end moves before a window that
covers it and starts after the start. Each pass reads every window; the bounds
only move inward, so they are stable after twice as many passes as there are
windows. An interval that empties is kept as it was. -/
def narrowInt (windows : List (Int × Int)) (c d : Int) : Int × Int :=
  let pass (lh : Int × Int) : Int × Int :=
    windows.foldl (fun (lh : Int × Int) (w : Int × Int) =>
      let lo := if w.1 ≤ lh.1 && lh.1 ≤ w.2 + 1 && w.2 < lh.2 then max lh.1 (w.2 + 1) else lh.1
      let hi := if lo < w.1 && w.1 ≤ lh.2 && lh.2 ≤ w.2 then min lh.2 (w.1 - 1) else lh.2
      (lo, hi)) lh
  let r := (List.range (2 * windows.length + 2)).foldl (fun lh _ => pass lh) (c, d)
  if r.1 ≤ r.2 then r else (c, d)

/-- An integer as a literal atom of sort `s`. -/
def intAtom (s : String) (n : Int) : STm := .atom (.lit s (toString n))

/-- The atom a row's value is, when it is one. -/
def atomOf? : STm → Option SAtom
  | .atom a => some a
  | .app _ _ _ => none

/-- An element of an interval operation: its key and its interval. -/
structure IRow where
  key : SAtom
  lo : Int
  hi : Int
  sort : String
  /-- The number of times the element occurs in a row. -/
  reps : Nat := 1

/-- The elements `(key, [lo, hi])` of three columns side by side. -/
def iRows (ks ls us : List (STm × Nat × Nat)) : Option (List IRow) :=
  (besides [ks, ls, us]).mapM fun (x : List (STm × Nat) × Nat) =>
    match x.1 with
    | [k, a, b] =>
      (atomOf? k.1).bind fun k => (intOf a.1).bind fun a => (intOf b.1).map fun b =>
        ({ key := k, lo := a.1, hi := b.1, sort := a.2, reps := x.2 } : IRow)
    | _ => none

/-- `(union-by p l u)`: per key, in the order of first sight, the union of
its intervals; a row is the key and one interval. An interval given twice is
given once: the union is the same. -/
def unionByRows (ps ls us : List (STm × Nat × Nat)) : Option (List (List STm × Nat × Nat)) :=
  (iRows ps ls us).map fun (xs : List IRow) =>
    let keys : List SAtom := xs.foldl (fun ks x => if ks.contains x.key then ks else ks ++ [x.key]) []
    let sort : String := (xs.head?.map (·.sort)).getD "i64"
    keys.flatMap fun g =>
      (unionInts ((xs.filter (·.key == g)).map fun x => (x.lo, x.hi))).map fun (ab : Int × Int) =>
        ([STm.atom g, intAtom sort ab.1, intAtom sort ab.2], 1, 1)

/-- `(narrow c d r a b q)`: per element `(r, [c, d])`, the interval narrowed
past the union of the intervals `[a, b]` whose key `q` is `r`; with `changed`,
only the rows whose interval changed. -/
def narrowRows (cs ds rs as bs qs : List (STm × Nat × Nat)) (changed : Bool) :
    Option (List (List STm × Nat × Nat)) :=
  (iRows qs as bs).bind fun (ws : List IRow) => (iRows rs cs ds).map fun (fs : List IRow) =>
    fs.filterMap fun f =>
      let windows := unionInts ((ws.filter (·.key == f.key)).map fun w => (w.lo, w.hi))
      let r := narrowInt windows f.lo f.hi
      if !changed || r.1 != f.lo || r.2 != f.hi then
        some ([STm.atom f.key, intAtom f.sort r.1, intAtom f.sort r.2], 1, f.reps)
      else none

/-- The rows a comprehension ranges over: each the values of its binders, a
count, and the number of times the row occurs in a row. Side by side, the
rows stop at the shortest sequence and take the first one's counts. -/
def rowsOf (r : SeqRule) (B : SBind) (grouped : Bool) : SSrc → Option (List (List STm × Nat × Nat))
  | .one x => (srcRows r B grouped x).map (·.map fun (t, k, m) => ([t], k, m))
  | .concat xs =>
    (xs.mapM (srcRows r B grouped)).map fun ls => ls.flatten.map fun (t, k, m) => ([t], k, m)
  | .zip xs =>
    (xs.mapM (srcRows r B grouped)).map fun ls =>
      (besides ls).map fun (hs, m) => (hs.map (·.1), (hs.head?.map (·.2)).getD 1, m)
  | .unionBy p l u =>
    (srcRows r B grouped p).bind fun ps => (srcRows r B grouped l).bind fun ls =>
      (srcRows r B grouped u).bind fun us => unionByRows ps ls us
  | .narrow c d rr a b q changed =>
    (srcRows r B grouped c).bind fun cs => (srcRows r B grouped d).bind fun ds =>
      (srcRows r B grouped rr).bind fun rs => (srcRows r B grouped a).bind fun as =>
        (srcRows r B grouped b).bind fun bs => (srcRows r B grouped q).bind fun qs =>
          narrowRows cs ds rs as bs qs changed

/-- The arguments a left-side item stands for, each with its count. -/
def SItem.args (B : SBind) : SItem → Option (List (STm × Nat))
  | .rest x => (B.seqs.lookup x).map (·.map fun ak => (STm.atom ak.1, ak.2))
  | .filter g p => (B.counts.lookup g).bind (B.rowsFrom p 0)
  | .one p => (patB B (B.look none) p).map fun t => [(t, 1)]

def itemsArgs (B : SBind) : List SItem → Option (List (STm × Nat))
  | [] => some []
  | it :: its => (it.args B).bind fun a => (itemsArgs B its).map (a ++ ·)

/-- What `..x` splices: the elements of the filter named `x`, else the rest
sequence `x`. -/
def spliceOf (r : SeqRule) (B : SBind) (x : String) : Option (List (STm × Nat)) :=
  match r.items.find? (fun it => match it with | .filter g _ => g == x | _ => false) with
  | some it => it.args B
  | none => (B.seqs.lookup x).map (·.map fun ak => (STm.atom ak.1, ak.2))

/-- Rows with the position each starts at, from position `i` on. A row that
occurs several times in a row is given once per position where a column of
length `L` has an entry, which the row reads there, and once for its
occurrences past the column. -/
def placeRows (L : Nat) : Nat → List (List STm × Nat × Nat) → List (List STm × Nat × Nat × Nat)
  | _, [] => []
  | i, (vs, k, m) :: rest =>
    ((List.range (min m (L - i))).map fun j => (vs, k, 1, i + j)) ++
      (if m > min m (L - i) then [(vs, k, m - min m (L - i), i + min m (L - i))] else []) ++
      placeRows L (i + m) rest

/-- What a comprehension binds while its body is built. -/
structure SLoc where
  vals : List (String × STm) := []
  cnts : List (String × Nat) := []

mutual

/-- The value of `e` under the binding: a filter's count is the number of its
elements, as an `i64`. -/
def numS (r : SeqRule) (B : SBind) (lc : SLoc) : SNum → Option Val
  | .rows src =>
    (rowsOf r B false src).map fun rows => .i64 ((rows.foldl (fun n row => n + row.2.2) 0 : Nat) : Int)
  | .agg op e =>
    -- `e` at each element: the filters' variables read at that element.
    let n := (B.cols.map (·.2.length)).foldl max 0
    ((List.range n).mapM fun i =>
      let cols : List (String × STm) := B.cols.filterMap fun (ca : String × List SAtom) =>
        (ca.2[i]?).map fun a => (ca.1, STm.atom a)
      numS r B { lc with vals := cols ++ lc.vals } e).bind fun vs =>
      match vs with
      | [] => if op == "sum" then some (.i64 0) else none
      | v :: rest =>
        let f := v.sortName ++ "::" ++ (if op == "sum" then "+" else op)
        rest.foldlM (fun acc x => primEval f [acc, x]) v
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
  | .prim f args => (numsS r B lc args).bind (primEval f)

def numsS (r : SeqRule) (B : SBind) (lc : SLoc) : List SNum → Option (List Val)
  | [] => some []
  | e :: es => (numS r B lc e).bind fun v => (numsS r B lc es).map (v :: ·)

end

/-- Whether the condition `g`, when there is one, computes `true`. -/
def holdsS (r : SeqRule) (B : SBind) (lc : SLoc) : Option SNum → Option Bool
  | none => some true
  | some g =>
    match numS r B lc g with
    | some (.bool b) => some b
    | _ => none

/-- The count `k` computes, 1 without it. -/
def timesS (r : SeqRule) (B : SBind) (lc : SLoc) : Option SNum → Option Nat
  | none => some 1
  | some k => (numS r B lc k).bind Val.toNat?

mutual

def rhsS (r : SeqRule) (B : SBind) (lc : SLoc) : SRhs → Option STm
  | .val e => (numS r B lc e).bind fun v => v.spell.map fun t => .atom (.lit v.sortName t)
  | .ite c a b => (holdsS r B lc (some c)).bind fun ok => if ok then rhsS r B lc a else rhsS r B lc b
  | .var x =>
    match lc.vals.lookup x with
    | some t => some t
    | none => (B.scalars.lookup x).map .atom
  | .lit s v => some (.atom (.lit s v))
  | .app f args => (argsS r B lc args).map (STm.mk f)

def argsS (r : SeqRule) (B : SBind) (lc : SLoc) : List SArg → Option (List (STm × Nat))
  | [] => some []
  | .tm t :: as => (rhsS r B lc t).bind fun x => (argsS r B lc as).map ((x, 1) :: ·)
  | .splice x :: as => (spliceOf r B x).bind fun xs => (argsS r B lc as).map (xs ++ ·)
  | .times t k :: as =>
    (timesS r B lc (some k)).bind fun n => (rhsS r B lc t).bind fun x =>
      (argsS r B lc as).map ((x, n) :: ·)
  | .comp body bs kv src grouped guard mult :: as =>
    (rowsOf r B grouped src).bind fun rows =>
      ((placeRows ((B.cols.map (·.2.length)).foldl max 0) 0 rows).mapM
        fun (row : List STm × Nat × Nat × Nat) =>
        -- The row at position `i` also reads each filter variable at element `i`.
        let cols : List (String × STm) := B.cols.filterMap fun (ca : String × List SAtom) =>
          (ca.2[row.2.2.2]?).map fun a => (ca.1, STm.atom a)
        let lc' : SLoc := { vals := bs.zip row.1 ++ cols ++ lc.vals,
                            cnts := (match kv with | some x => [(x, row.2.1)] | none => []) ++ lc.cnts }
        (holdsS r B lc' guard).bind fun ok =>
          if ok then
            -- The body with its count, once per occurrence of the row.
            (timesS r B lc' mult).bind fun n => (rhsS r B lc' body).map fun t => [(t, n * row.2.2.1)]
          else some []).bind fun parts =>
        (argsS r B lc as).map (parts.flatten ++ ·)

end

/-- The two terms rule `r` equates under binding `B`, when each of its
conditions computes `true` and each element of a counted filter has at least
the filter's least count. -/
def seqApply (r : SeqRule) (B : SBind) : Option (STm × STm) :=
  -- The `:let` names, in order: each the literal its value is.
  let lc : Option SLoc := r.lets.foldl (fun (lc : Option SLoc) (xe : String × SNum) =>
    lc.bind fun lc => (numS r B lc xe.2).bind fun v => v.spell.map fun t =>
      { lc with vals := (xe.1, STm.atom (.lit v.sortName t)) :: lc.vals }) (some {})
  match lc with
  | none => none
  | some lc =>
  if !(r.guards.all fun g => holdsS r B lc (some g) == some true) then none
  else if !(r.least.all fun (g, n) => match B.counts.lookup g with
      | some ks => ks.all (n ≤ ·)
      | none => false) then none
  else
    let L := match r.lhs with
      | some p => patB B (B.look none) p
      | none => (itemsArgs B r.items).map (STm.mk r.op)
    L.bind fun L => (rhsS r B lc r.rhs).map fun R => (L, R)

/-! ## Rules that read a sequence as a whole

The statement admits a sequence rule under every binding, and the engine
fires it under the binding whose filters hold every matching argument. A rule
whose result reads a filter or a rest sequence as a whole (its number of
elements, a sum or a fold over them, an interval union) yields another
equality under a binding that leaves a matching argument in the rest. The
functions below recognize these rules, for the replay's report: they are no
part of the statement. -/

mutual

def SNum.whole : SNum → Bool
  | .count _ => true
  | .sum _ => true
  | .rows _ => true
  | .agg _ _ => true
  | .prim _ args => SNum.wholes args
  | .lit _ _ => false
  | .var _ => false
  | .cnt _ _ => false

def SNum.wholes : List SNum → Bool
  | [] => false
  | e :: es => e.whole || SNum.wholes es

end

def SSrc.whole : SSrc → Bool
  | .unionBy _ _ _ => true
  | .narrow _ _ _ _ _ _ _ => true
  | _ => false

mutual

def SRhs.whole : SRhs → Bool
  | .var _ => false
  | .lit _ _ => false
  | .app _ args => SArg.wholes args
  | .val e => e.whole
  | .ite c a b => c.whole || a.whole || b.whole

def SArg.wholes : List SArg → Bool
  | [] => false
  | .tm t :: as => t.whole || SArg.wholes as
  | .splice _ :: as => SArg.wholes as
  | .times t k :: as => t.whole || k.whole || SArg.wholes as
  | .comp body _ _ src _ guard mult :: as =>
    body.whole || src.whole || (match guard with | some g => g.whole | none => false) ||
      (match mult with | some k => k.whole | none => false) || SArg.wholes as

end

/-- The rule's result reads a sequence as a whole, and its left side has a
rest sequence beside a filter: a binding can leave a matching argument in the
rest, and the rule then yields another equality than under the binding the
engine fires it with. -/
def SeqRule.whole (r : SeqRule) : Bool :=
  (r.rhs.whole || r.guards.any SNum.whole || r.lets.any (·.2.whole)) &&
    r.items.any (fun it => match it with | .filter _ _ => true | _ => false) &&
    r.items.any (fun it => match it with | .rest _ => true | _ => false)

end SemperCheck

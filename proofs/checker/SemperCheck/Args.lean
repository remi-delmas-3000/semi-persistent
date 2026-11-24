import Std.Data.HashSet

/-!
# Argument lists in run-length form

The replayer reads every application's arguments as runs: a node and the
number of consecutive times it occurs. A multiset operator's node holds its
children this way (`Node.napp`), so a count is never written as repeated
arguments: each operation below costs the number of runs, not the number of
arguments. A positional operator's argument list is the same list with each
run of equal neighbours as one entry, which loses nothing.

This file is part of the replayer, which the soundness statement does not
depend on: the kernel checks every step the replayer derives from these lists.
-/

namespace SemperCheck.Replay

/-- An argument list as runs. No run has count zero and no two neighbouring
runs hold the same node, so two lists are equal exactly when their runs are. -/
structure Args where
  runs : List (Nat × Nat)
deriving BEq, Repr, Inhabited

namespace Args

/-- Runs without a zero count, neighbouring runs of one node added. -/
def norm : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | (c, k) :: t =>
    if k = 0 then norm t
    else
      match norm t with
      | (d, j) :: r => if c = d then (d, j + k) :: r else (c, k) :: (d, j) :: r
      | [] => [(c, k)]

def ofRuns (l : List (Nat × Nat)) : Args := ⟨norm l⟩

def ofList (l : List Nat) : Args := ⟨norm (l.map fun c => (c, 1))⟩

def nil : Args := ⟨[]⟩

def one (a : Nat) : Args := ⟨[(a, 1)]⟩

/-- `a`, `k` times. -/
def rep (k a : Nat) : Args := if k = 0 then nil else ⟨[(a, k)]⟩

/-- Every argument, a run's node as many times as its count: for a positional
operator's node, whose arguments the table holds one by one. -/
def toList (xs : Args) : List Nat := xs.runs.flatMap fun ck => List.replicate ck.2 ck.1

/-- The number of arguments. -/
def length (xs : Args) : Nat := xs.runs.foldl (fun n ck => n + ck.2) 0

def isEmpty (xs : Args) : Bool := xs.runs.isEmpty

def append (xs ys : Args) : Args := ⟨norm (xs.runs ++ ys.runs)⟩

instance : Append Args := ⟨append⟩

instance : ToString Args where
  toString xs := toString (xs.runs.map fun ck => if ck.2 == 1 then toString ck.1 else s!"{ck.1}:{ck.2}")

def map (xs : Args) (g : Nat → Nat) : Args := ⟨norm (xs.runs.map fun ck => (g ck.1, ck.2))⟩

def filter (xs : Args) (p : Nat → Bool) : Args := ⟨norm (xs.runs.filter fun ck => p ck.1)⟩

/-- `xs`, `k` times. A multiset (`bag`) multiplies each count; a sequence of
more than one run is repeated run by run. -/
def times (bag : Bool) (k : Nat) (xs : Args) : Args :=
  if k = 0 then nil
  else if k = 1 then xs
  else if bag || xs.runs.length ≤ 1 then ⟨xs.runs.map fun ck => (ck.1, ck.2 * k)⟩
  else ⟨norm (List.replicate k xs.runs).flatten⟩

/-- Each argument replaced by the arguments `g` gives for it. -/
def bind (bag : Bool) (xs : Args) (g : Nat → Args) : Args :=
  ⟨norm (xs.runs.flatMap fun ck => (times bag ck.2 (g ck.1)).runs)⟩

/-- The number of times `a` occurs. -/
def count (xs : Args) (a : Nat) : Nat :=
  xs.runs.foldl (fun n ck => if ck.1 == a then n + ck.2 else n) 0

def contains (xs : Args) (a : Nat) : Bool := xs.runs.any fun ck => ck.1 == a

def all (xs : Args) (p : Nat → Bool) : Bool := xs.runs.all fun ck => p ck.1

def any (xs : Args) (p : Nat → Bool) : Bool := xs.runs.any fun ck => p ck.1

def find? (xs : Args) (p : Nat → Bool) : Option Nat := (xs.runs.find? fun ck => p ck.1).map (·.1)

def head? (xs : Args) : Option Nat := xs.runs.head?.map (·.1)

def getLast? (xs : Args) : Option Nat := xs.runs.getLast?.map (·.1)

/-- The one argument of a list of one. -/
def single? (xs : Args) : Option Nat :=
  match xs.runs with
  | [(c, 1)] => some c
  | _ => none

/-- The distinct nodes, in the order of their first occurrence. -/
def keys (xs : Args) : List Nat :=
  (xs.runs.foldl (fun (acc : Array Nat × Std.HashSet Nat) ck =>
    if acc.2.contains ck.1 then acc else (acc.1.push ck.1, acc.2.insert ck.1)) (#[], {})).1.toList

/-- Each distinct node once. -/
def dedup (xs : Args) : Args := ⟨xs.keys.map fun c => (c, 1)⟩

/-- The arguments in the order of node ids: each node is then one run. -/
def sort (xs : Args) : Args := ⟨norm (xs.runs.mergeSort fun a b => a.1 ≤ b.1)⟩

def eraseRuns (a : Nat) : List (Nat × Nat) → Nat → List (Nat × Nat)
  | [], _ => []
  | (c, j) :: t, k =>
    if k = 0 then (c, j) :: t
    else if c = a then (if j ≤ k then eraseRuns a t (k - j) else (c, j - k) :: t)
    else (c, j) :: eraseRuns a t k

/-- Without the first `k` occurrences of `a`. -/
def eraseN (xs : Args) (a k : Nat) : Args := ⟨norm (eraseRuns a xs.runs k)⟩

/-- Without the first occurrence of `a`. -/
def erase (xs : Args) (a : Nat) : Args := xs.eraseN a 1

def takeRuns : List (Nat × Nat) → Nat → List (Nat × Nat)
  | [], _ => []
  | (c, j) :: t, n =>
    if n = 0 then [] else if j ≤ n then (c, j) :: takeRuns t (n - j) else [(c, n)]

def dropRuns : List (Nat × Nat) → Nat → List (Nat × Nat)
  | [], _ => []
  | (c, j) :: t, n =>
    if n = 0 then (c, j) :: t else if j ≤ n then dropRuns t (n - j) else (c, j - n) :: t

/-- The first `n` arguments. -/
def take (xs : Args) (n : Nat) : Args := ⟨takeRuns xs.runs n⟩

/-- Without the first `n` arguments. -/
def drop (xs : Args) (n : Nat) : Args := ⟨dropRuns xs.runs n⟩

/-- The runs of two lists paired position by position: a run longer than the
one it faces is split. `none` when the lists differ in length. -/
def zipRuns : Nat → List (Nat × Nat) → List (Nat × Nat) → Option (List (Nat × Nat))
  | _, [], [] => some []
  | 0, _, _ => none
  | n + 1, (c, k) :: t, (d, j) :: u =>
    if k == j then (zipRuns n t u).map ((c, d) :: ·)
    else if k < j then (zipRuns n t ((d, j - k) :: u)).map ((c, d) :: ·)
    else (zipRuns n ((c, k - j) :: t) u).map ((c, d) :: ·)
  | _, _, _ => none

/-- The arguments of two lists of one length, position by position: each pair
of nodes that face each other, once per pair of runs. -/
def pairs? (xs ys : Args) : Option (List (Nat × Nat)) :=
  zipRuns (xs.runs.length + ys.runs.length + 1) xs.runs ys.runs

end Args

end SemperCheck.Replay

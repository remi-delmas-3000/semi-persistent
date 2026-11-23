import SemperCheck.Syntax

/-!
# What a sequence rule yields under a binding

`seqApply r B` is the pair of terms rule `r` equates under the binding `B`:
the left side is the root operator applied to its items (a rest sequence
gives its atoms, a filter gives one instance of its pattern per element, as
many times as the element's count), and the right side is built from the same
elements. It is part of the statement of the soundness theorem: a model
satisfies `r` when the two terms are equal under every binding and every
valuation of the atoms (`Semantics.lean`, `SeqSat`).

A binding names what one firing collected. The statement does not ask that
the filter's elements be all the arguments that match its pattern.
-/

namespace SemperCheck

mutual

/-- Pattern `p` with each variable read by `look`. A rest variable or a
counted argument has no instance here. -/
def patS (look : String → Option SAtom) : Pat → Option STm
  | .var x => (look x).map .atom
  | .lit s v => some (.atom (.lit s v))
  | .app f ps => (patsS look ps).map (.app f)
  | .rest _ => none
  | .rep _ _ => none
  | .times _ _ => none
  | .count _ => none

def patsS (look : String → Option SAtom) : List Pat → Option (List STm)
  | [] => some []
  | p :: ps => (patS look p).bind fun t => (patsS look ps).map (t :: ·)

end

namespace SBind

/-- The value of variable `x` at element `i` of a filter: its column's entry,
or the scalar. -/
def look (B : SBind) (i : Option Nat) (x : String) : Option SAtom :=
  match i.bind fun i => (B.cols.lookup x).bind (·[i]?) with
  | some a => some a
  | none => B.scalars.lookup x

/-- The instances of pattern `p` at the elements whose counts are `ks`,
starting at element `i`: element `j` gives its instance `ks[j]` times. -/
def elemsFrom (B : SBind) (p : Pat) (i : Nat) : List Nat → Option (List STm)
  | [] => some []
  | k :: ks =>
    (patS (B.look (some i)) p).bind fun t =>
      (elemsFrom B p (i + 1) ks).map (List.replicate k t ++ ·)

end SBind

/-- The arguments a left-side item stands for. -/
def SItem.args (B : SBind) : SItem → Option (List STm)
  | .rest x => (B.seqs.lookup x).map (·.map .atom)
  | .filter g p => (B.counts.lookup g).bind (B.elemsFrom p 0)
  | .one p => (patS (B.look none) p).map ([·])

def itemsArgs (B : SBind) : List SItem → Option (List STm)
  | [] => some []
  | it :: its => (it.args B).bind fun a => (itemsArgs B its).map (a ++ ·)

/-- What `..x` splices: the elements of the filter named `x`, else the rest
sequence `x`. -/
def spliceOf (r : SeqRule) (B : SBind) (x : String) : Option (List STm) :=
  match r.items.find? (fun it => match it with | .filter g _ => g == x | _ => false) with
  | some it => it.args B
  | none => (B.seqs.lookup x).map (·.map .atom)

mutual

def rhsS (r : SeqRule) (B : SBind) : SRhs → Option STm
  | .var x => (B.scalars.lookup x).map .atom
  | .lit s v => some (.atom (.lit s v))
  | .app f args => (argsS r B args).map (.app f)

def argsS (r : SeqRule) (B : SBind) : List SArg → Option (List STm)
  | [] => some []
  | .tm t :: as => (rhsS r B t).bind fun x => (argsS r B as).map (x :: ·)
  | .splice x :: as => (spliceOf r B x).bind fun xs => (argsS r B as).map (xs ++ ·)

end

/-- The two terms rule `r` equates under binding `B`. -/
def seqApply (r : SeqRule) (B : SBind) : Option (STm × STm) :=
  (itemsArgs B r.items).bind fun ls => (rhsS r B r.rhs).map fun R => (.app r.op ls, R)

end SemperCheck

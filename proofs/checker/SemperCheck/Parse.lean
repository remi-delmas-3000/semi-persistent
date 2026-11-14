import SemperCheck.Kernel

/-!
# Reading a program and a certificate

The `.egg` reader is trusted: the soundness theorem is about the `Program` it
returns. It reads every command that states or asks for an equality, and it
reads them so that the theory it returns is implied by the program's:

* An operator's laws come from its declaration's algebraic tags. A tag the
  reader does not model (`:nilpotent`, `:inverse`, `:cancellative`,
  `:assoc-left`, `:assoc-right`) is dropped, which leaves the operator with
  fewer laws than the engine gives it.
* A rule whose pattern or guard uses a rest variable, a multiplicity, a
  filter, a primitive predicate or a comprehension states something the
  `Rule` type cannot; the reader keeps its position and no rule of it, so no
  certificate can cite it.
* A bare identifier is a global if a `let` names it, else a nullary
  application if an operator of that name is declared, else a pattern
  variable: reading as a variable a name the engine reads as a constant
  would state a stronger rule than the program's.
* A program with `push`, `pop` or `include` is rejected: a command after a
  `pop` would be checked against commands the program retracted.

Commands that state no equality (`run`, `extract`, `check-neq`, ground term
insertions) are skipped.
-/

namespace SemperCheck

inductive SExp where
  | atom (s : String)
  | list (xs : List SExp)
  deriving Repr, Inhabited

/-! ## S-expressions with the byte offset of each top-level form -/

partial def skipWs (cs : List Char) (pos : Nat) : List Char × Nat :=
  match cs with
  | c :: rest =>
    if c == ';' then
      let (rest', pos') := skipLine rest (pos + 1)
      skipWs rest' pos'
    else if c.isWhitespace then skipWs rest (pos + c.utf8Size)
    else (cs, pos)
  | [] => ([], pos)
where
  skipLine : List Char → Nat → List Char × Nat
    | '\n' :: rest, pos => (rest, pos + 1)
    | c :: rest, pos => skipLine rest (pos + c.utf8Size)
    | [], pos => ([], pos)

partial def readAtom (cs : List Char) (pos : Nat) (acc : String) : String × List Char × Nat :=
  match cs with
  | c :: rest =>
    if c.isWhitespace || c == '(' || c == ')' || c == ';' then (acc, cs, pos)
    else readAtom rest (pos + c.utf8Size) (acc.push c)
  | [] => (acc, [], pos)

partial def readString (cs : List Char) (pos : Nat) (acc : String) :
    Except String (String × List Char × Nat) :=
  match cs with
  | '\\' :: c :: rest => readString rest (pos + 1 + c.utf8Size) ((acc.push '\\').push c)
  | '"' :: rest => .ok (acc.push '"', rest, pos + 1)
  | c :: rest => readString rest (pos + c.utf8Size) (acc.push c)
  | [] => .error "unterminated string"

partial def readSExp (cs : List Char) (pos : Nat) : Except String (SExp × List Char × Nat) := do
  let (cs, pos) := skipWs cs pos
  match cs with
  | '(' :: rest => readList rest (pos + 1) #[]
  | ')' :: _ => .error s!"unexpected ')' at byte {pos}"
  | '"' :: rest =>
    let (s, rest, pos) ← readString rest (pos + 1) "\""
    return (.atom s, rest, pos)
  | [] => .error "unexpected end of input"
  | _ =>
    let (a, rest, pos) := readAtom cs pos ""
    return (.atom a, rest, pos)
where
  readList (cs : List Char) (pos : Nat) (acc : Array SExp) :
      Except String (SExp × List Char × Nat) := do
    let (cs, pos) := skipWs cs pos
    match cs with
    | ')' :: rest => return (.list acc.toList, rest, pos + 1)
    | [] => .error "unclosed '('"
    | _ =>
      let (x, rest, pos) ← readSExp cs pos
      readList rest pos (acc.push x)

/-- The top-level forms with their byte offsets. -/
partial def readTop (src : String) : Except String (List (Nat × SExp)) :=
  go src.toList 0 #[]
where
  go (cs : List Char) (pos : Nat) (acc : Array (Nat × SExp)) :
      Except String (List (Nat × SExp)) := do
    let (cs, pos) := skipWs cs pos
    match cs with
    | [] => return acc.toList
    | _ =>
      let (x, rest, pos') ← readSExp cs pos
      go rest pos' (acc.push (pos, x))

/-! ## The program -/

def isLiteral (a : String) : Bool :=
  match a.toList with
  | c :: _ => c.isDigit || c == '"' || c == '-' && a.length > 1 || a == "true" || a == "false"
  | [] => false

/-- The sorts of the engine's literals. -/
def litSorts : List String :=
  ["i64", "u64", "f64", "usize", "String", "bool", "IBig", "UBig", "RBig"]

/-- The sort of literal `a` at a position of sort `exp`: `exp` itself when a
literal of that spelling can be of that sort, else none; with no expected
sort, the engine's default for the spelling (`String`, `bool`, `f64` for a
spelling with a point, else `i64`). -/
def litSort (exp : Option String) (a : String) : Option String :=
  let str := a.startsWith "\""
  let bool := a == "true" || a == "false"
  let ok (s : String) : Bool :=
    if str then s == "String" else if bool then s == "bool"
    else s != "String" && s != "bool" && litSorts.contains s
  match exp with
  | some s => if ok s then some s else none
  | none =>
    if str then some "String" else if bool then some "bool"
    else if a.contains '.' then some "f64" else some "i64"

structure Env where
  /-- Each `let` name with its term and the term's sort. -/
  globals : List (String × (Term × String)) := []
  /-- The operators declared so far, in order. -/
  ops : List OpDecl := []

def Env.op? (E : Env) (f : String) : Option OpDecl := E.ops.find? (·.name == f)

/-- The sort an argument at position `i` of `d` takes. -/
def argSort (d : OpDecl) (i : Nat) : Option String :=
  if d.kind.isAssoc then some d.res else d.args[i]?

def checkSort (exp : Option String) (s : String) : Except String Unit :=
  match exp with
  | some e => if e == s then pure () else throw s!"sort {s} where {e} is expected"
  | none => pure ()

/-- A ground term and its sort, read at a position of sort `exp`. Counted
children (`t :k`, `t:k`) are expanded. -/
partial def Env.term (E : Env) (exp : Option String) : SExp → Except String (Term × String)
  | .atom a =>
    if isLiteral a then
      match litSort exp a with
      | some s => pure (.lit s a, s)
      | none => throw s!"literal {a} where {exp.getD ""} is expected"
    else match E.globals.lookup a with
      | some (t, s) => do checkSort exp s; pure (t, s)
      | none =>
        match E.op? a with
        | some d => do
          unless d.kind.isAssoc || d.args.isEmpty do throw s!"{a} takes arguments"
          checkSort exp d.res
          pure (.app a [], d.res)
        | none => throw s!"unknown name {a}"
  | .list (.atom f :: args) => do
    let some d := E.op? f | throw s!"unknown operator {f}"
    checkSort exp d.res
    let mut out : Array Term := #[]
    for x in args do
      let i := out.size
      match x with
      | .atom a =>
        if a.startsWith ":" then
          let some k := (a.drop 1).toString.toNat? | throw s!"unsupported child tag {a}"
          if k > 65536 then throw s!"count {k} above 65536"
          let some last := out.back? | throw s!"count without a child in {f}"
          out := out.pop
          for _ in [0:k] do out := out.push last
        else if (a.splitOn ":").length == 2 && !isLiteral a then
          match a.splitOn ":" with
          | [n, k] =>
            let some k := k.toNat? | throw s!"unsupported child {a}"
            if k > 65536 then throw s!"count {k} above 65536"
            let (t, _) ← E.term (argSort d i) (.atom n)
            for _ in [0:k] do out := out.push t
          | _ => throw s!"unsupported child {a}"
        else out := out.push (← E.term (argSort d i) x).1
      | _ => out := out.push (← E.term (argSort d i) x).1
    unless d.kind.isAssoc || out.size == d.args.length do
      throw s!"{f} takes {d.args.length} arguments"
    return (.app f out.toList, d.res)
  | x => .error s!"not a term: {repr x}"

/-- What reading a rule's patterns has learned: each variable's sort, and the
pairs of variables an equality between two unsorted variables relates. -/
structure VarSorts where
  sorts : List (String × String) := []
  pending : List (String × String) := []

abbrev PatM := StateT VarSorts Option

def setSort (x s : String) : PatM Unit := do
  let st ← get
  match st.sorts.lookup x with
  | some t => if t == s then pure () else failure
  | none => set { st with sorts := (x, s) :: st.sorts }

def ofTerm : Term → Pat
  | .lit s v => .lit s v
  | .app f args => .app f (args.map ofTerm)

/-- A pattern at a position of sort `exp`, and its sort if known; fails on a
construct the `Pat` type does not express and on a sort conflict. -/
partial def Env.pat (E : Env) (exp : Option String) : SExp → PatM (Pat × Option String)
  | .atom a =>
    if isLiteral a then
      match litSort exp a with
      | some s => pure (.lit s a, some s)
      | none => failure
    else if a.startsWith ".." || a.startsWith ":" || (a.splitOn ":").length > 1 then failure
    else match E.globals.lookup a with
      | some (t, s) => do
        if exp.isSome && exp != some s then failure
        pure (ofTerm t, some s)
      | none =>
        match E.op? a with
        | some d => do
          unless d.kind.isAssoc || d.args.isEmpty do failure
          if exp.isSome && exp != some d.res then failure
          pure (.app a [], some d.res)
        | none => do
          match exp with
          | some s => setSort a s; pure (.var a, some s)
          | none => pure (.var a, (← get).sorts.lookup a)
  | .list (.atom f :: args) => do
    if f == "=" then failure
    let some d := E.op? f | failure
    if exp.isSome && exp != some d.res then failure
    unless d.kind.isAssoc || args.length == d.args.length do failure
    let mut ps : Array Pat := #[]
    for x in args do
      let (p, _) ← E.pat (argSort d ps.size) x
      ps := ps.push p
    pure (.app f ps.toList, some d.res)
  | _ => failure

/-- An equality between two patterns: the second is read at the first's
sort, and a variable on the left takes the right's sort. -/
def Env.eqn (E : Env) (p q : SExp) : PatM (Pat × Pat) := do
  let (pp, sp) ← E.pat none p
  let (qq, sq) ← E.pat sp q
  match sp, sq, pp, qq with
  | none, some s, .var x, _ => setSort x s
  | none, none, .var x, .var y => modify fun st => { st with pending := (x, y) :: st.pending }
  | _, _, _, _ => pure ()
  pure (pp, qq)

/-- A body atom or guard: an equality, or a pattern that only asks for a term
to exist (no constraint in a model, whose operators are total). -/
def Env.guard (E : Env) : SExp → PatM (List (Pat × Pat))
  | .list [.atom "=", p, q] => do return [← E.eqn p q]
  | x => do let _ ← E.pat none x; return []

/-- Gives the pending pairs of variables their sorts, until none changes. -/
def settle : Nat → PatM Unit
  | 0 => pure ()
  | n + 1 => do
    let st ← get
    let mut changed := false
    for (x, y) in st.pending do
      match (← get).sorts.lookup x, (← get).sorts.lookup y with
      | some s, none => setSort y s; changed := true
      | none, some s => setSort x s; changed := true
      | some s, some t => if s != t then failure
      | none, none => pure ()
    if changed then settle n

/-- The rule, when every variable has a sort. -/
def finish (lhs rhs : Pat) (eqs : List (Pat × Pat)) : PatM Rule := do
  settle 64
  let st ← get
  let r : Rule := { lhs, rhs, eqs, sorts := st.sorts }
  unless r.vars.all fun x => (st.sorts.lookup x).isSome do failure
  pure r

def kindOf (tags : List String) : Kind :=
  let a := tags.contains ":assoc" || tags.contains ":assoc-comm" || tags.contains ":assoc-comm-idem"
  let c := tags.contains ":comm" || tags.contains ":assoc-comm" || tags.contains ":assoc-comm-idem"
  let i := tags.contains ":assoc-comm-idem" || tags.contains ":idempotent"
  if a && c && i then .aci
  else if a && c then .ac
  else if a then .assoc
  else if c then .comm
  else .plain

def atoms : List SExp → List String
  | .atom a :: xs => a :: atoms xs
  | _ :: xs => atoms xs
  | [] => []

/-- The `:identity` argument, if any. -/
def identityOf : List SExp → Option SExp
  | .atom ":identity" :: t :: _ => some t
  | _ :: xs => identityOf xs
  | [] => none

/-- The value after tag `k` in a tag list. -/
def tagArg (k : String) : List SExp → Option SExp
  | .atom a :: v :: xs => if a == k then some v else tagArg k (v :: xs)
  | _ :: xs => tagArg k xs
  | [] => none

/-- The rule of a `rewrite`: `lhs` (whose root binding `(= v p)` becomes an
equality premise) to `rhs`, under the `:when` guards. -/
def Env.rewriteRule (E : Env) (lhs rhs : SExp) (tags : List SExp) : Option Rule :=
  if tags.any (fun t => match t with | .atom ":let" => true | _ => false) then none
  else (go.run {}).map (·.1)
where
  go : PatM Rule := do
    let (l, root) ← match lhs with
      | .list [.atom "=", .atom v, p] => do
        let (pp, sp) ← E.pat none p
        if let some s := sp then setSort v s
        pure (pp, [(Pat.var v, pp)])
      | _ => do pure ((← E.pat none lhs).1, [])
    let gs ← match tagArg ":when" tags with
      | some (.list gs) => do
        let mut out := []
        for g in gs do out := out ++ (← E.guard g)
        pure out
      | some _ => failure
      | none => pure []
    let sl := (← E.pat none (match lhs with | .list [.atom "=", _, p] => p | _ => lhs)).2
    let (r, _) ← E.pat sl rhs
    finish l r (root ++ gs)

/-- The rules of a `rule`: one per `union` action, under the body's
equalities, with the action's `let` names expanded. -/
def Env.ruleRules (E : Env) (body actions : List SExp) : List (Option Rule) :=
  let unions := actions.filter fun a => match a with
    | .list [.atom "union", _, _] => true
    | _ => false
  match (go actions [] []).run {} with
  | some (rs, _) => rs
  | none => unions.map fun _ => none
where
  bodyEqs : PatM (List (Pat × Pat)) := do
    let mut out := []
    for g in body do out := out ++ (← E.guard g)
    pure out
  /-- One entry per `union` action; a failed action is `none`. -/
  go : List SExp → List (String × SExp) → List (Option Rule) → PatM (List (Option Rule))
    | .list [.atom "union", p, q] :: rest, lets, acc => do
      let st ← get
      let one : PatM Rule := do
        let eqs ← bodyEqs
        let (pp, qq) ← E.eqn (substS lets p) (substS lets q)
        finish pp qq eqs
      let r := (one.run st).map (·.1)
      go rest lets (acc ++ [r])
    | .list [.atom "let", .atom v, t] :: rest, lets, acc => go rest ((v, substS lets t) :: lets) acc
    | _ :: rest, lets, acc => go rest lets acc
    | [], _, acc => pure acc
  substS (lets : List (String × SExp)) : SExp → SExp
    | .atom x => (lets.lookup x).getD (.atom x)
    | .list xs => .list (xs.map (substS lets))

def declTags (xs : List SExp) : List SExp :=
  xs.dropWhile fun x => match x with | .atom a => !a.startsWith ":" | _ => true

/-- An operator declaration: `assoc`, `ac` and `aci` need one argument of the
result sort, and `comm` two of one sort; otherwise the operator gets no laws. -/
def Env.decl (E : Env) (f : String) (args : List String) (res : String) (tags : List SExp) :
    Except String OpDecl := do
  let k := kindOf (atoms tags)
  let k := if k.isAssoc && args != [res] then .plain
    else if k == .comm && !(args.length == 2 && args[0]? == args[1]?) then .plain
    else k
  let unit ← match identityOf tags with
    | some t => if k.isAssoc then some <$> (Prod.fst <$> E.term (some res) t) else pure none
    | none => pure none
  pure { name := f, kind := k, args, res, unit }

def sortNames : SExp → List String
  | .list xs => atoms xs
  | .atom a => [a]

/-- Reads one command. -/
def step (E : Env) (P : Program) (o : Nat) : SExp → Except String (Env × Program)
  | .list (.atom "function" :: .atom f :: args :: .atom res :: tags)
  | .list (.atom "constructor" :: .atom f :: args :: .atom res :: tags) => do
    let d ← E.decl f (sortNames args) res tags
    return ({ E with ops := E.ops ++ [d] }, { P with ops := P.ops ++ [d] })
  | .list (.atom "relation" :: .atom f :: args :: _) => do
    let d : OpDecl := { name := f, kind := .plain, args := sortNames args, res := "Unit" }
    return ({ E with ops := E.ops ++ [d] }, { P with ops := P.ops ++ [d] })
  | .list (.atom "datatype" :: .atom srt :: variants) => do
    let mut E := E
    let mut P := P
    for v in variants do
      if let .list (.atom f :: rest) := v then
        let tags := declTags rest
        let args := atoms (rest.take (rest.length - tags.length))
        let d ← E.decl f args srt tags
        E := { E with ops := E.ops ++ [d] }
        P := { P with ops := P.ops ++ [d] }
    return (E, P)
  | .list [.atom "let", .atom x, t] => do
    let ts ← E.term none t
    return ({ E with globals := (x, ts) :: E.globals }, P)
  | .list [.atom "union", a, b] => do
    let (ta, sa) ← E.term none a
    let (tb, _) ← E.term (some sa) b
    return (E, { P with decls := P.decls ++ [(o, .axiom ta tb)] })
  | .list [.atom "check-eq", a, b] => do
    let (ta, sa) ← E.term none a
    let (tb, _) ← E.term (some sa) b
    return (E, { P with decls := P.decls ++ [(o, .goal ta tb)] })
  | .list (.atom "rewrite" :: l :: r :: tags) =>
    return (E, { P with decls := P.decls ++ [(o, .rules [E.rewriteRule l r tags])] })
  | .list (.atom "birewrite" :: l :: r :: tags) =>
    return (E, { P with decls := P.decls ++
      [(o, .rules [E.rewriteRule l r tags, E.rewriteRule r l tags])] })
  | .list (.atom "rule" :: .list body :: .list actions :: _) =>
    return (E, { P with decls := P.decls ++ [(o, .rules (E.ruleRules body actions))] })
  | .list (.atom "push" :: _) | .list (.atom "pop" :: _) | .list (.atom "include" :: _) =>
    .error "push, pop and include are not supported"
  | _ => return (E, P)

def parseProgram (src : String) : Except String Program := do
  let forms ← readTop src
  let mut E : Env := {}
  let mut P : Program := { ops := [], litSorts, decls := [] }
  for (o, x) in forms do
    (E, P) ← step E P o x
  return P

/-! ## The certificate

```
semper-cert 1
n <id> a <op> <child>...
n <id> l <sort> <literal>
s <id> refl <a>
s <id> symm <s>
s <id> trans <s> <t>
s <id> axiom <offset> <a> <b>
s <id> rule <offset> <j> <a> <b> <n> (<var> <node>)^n <step>...
s <id> cong <op> <a> <b> <step>...
g <offset> <step>
```

Node and step ids count from 0 in order.
-/

def parseCert (src : String) : Except String Cert := do
  let lines := (src.splitOn "\n").filter fun l => !l.isEmpty && !l.startsWith "#"
  let some hdr := lines.head? | throw "empty certificate"
  unless hdr.startsWith "semper-cert 1" do throw s!"bad header {hdr}"
  let mut nodes : Array Node := #[]
  let mut steps : Array Step := #[]
  let mut goals : Array (Nat × Nat) := #[]
  for l in lines.drop 1 do
    let ws := (l.splitOn " ").filter (!·.isEmpty)
    let nat (s : String) : Except String Nat :=
      match s.toNat? with | some n => .ok n | none => .error s!"bad number {s} in: {l}"
    match ws with
    | "n" :: i :: "a" :: f :: cs =>
      unless (← nat i) == nodes.size do throw s!"node out of order: {l}"
      nodes := nodes.push (.app f (← cs.mapM nat))
    | "n" :: i :: "l" :: srt :: _ =>
      unless (← nat i) == nodes.size do throw s!"node out of order: {l}"
      let pre := s!"n {i} l {srt} "
      nodes := nodes.push (.lit srt (l.drop pre.length).toString)
    | "s" :: i :: k :: args =>
      unless (← nat i) == steps.size do throw s!"step out of order: {l}"
      let st ← match k, args with
        | "refl", [a] => pure (Step.refl (← nat a))
        | "symm", [s] => pure (.symm (← nat s))
        | "trans", [s, t] => pure (.trans (← nat s) (← nat t))
        | "axiom", [o, a, b] => pure (.axiom (← nat o) (← nat a) (← nat b))
        | "rule", o :: j :: a :: b :: n :: rest => do
          let n ← nat n
          let sig := rest.take (2 * n)
          let mut σ : Array (String × Nat) := #[]
          for k in [0:n] do
            σ := σ.push (sig[2 * k]!, ← nat sig[2 * k + 1]!)
          pure (.rule (← nat o) (← nat j) σ.toList (← (rest.drop (2 * n)).mapM nat) (← nat a) (← nat b))
        | "cong", f :: a :: b :: ps => pure (.cong f (← nat a) (← nat b) (← ps.mapM nat))
        | _, _ => throw s!"bad step: {l}"
      steps := steps.push st
    | ["g", o, s] => goals := goals.push (← nat o, ← nat s)
    | _ => throw s!"bad line: {l}"
  return { nodes, steps, goals := goals.toList }

end SemperCheck

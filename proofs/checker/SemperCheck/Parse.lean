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

structure Env where
  globals : List (String × Term) := []
  ops : List String := []

/-- A ground term. Counted children (`t :k`, `t:k`) are expanded. -/
partial def Env.term (E : Env) : SExp → Except String Term
  | .atom a =>
    if isLiteral a then .ok (.lit a)
    else match E.globals.lookup a with
      | some t => .ok t
      | none => if E.ops.contains a then .ok (.app a []) else .error s!"unknown name {a}"
  | .list (.atom f :: args) => do
    let mut out : Array Term := #[]
    for x in args do
      match x with
      | .atom a =>
        if a.startsWith ":" then
          let some k := (a.drop 1).toString.toNat? | throw s!"unsupported child tag {a}"
          let some last := out.back? | throw s!"count without a child in {f}"
          out := out.pop
          for _ in [0:k] do out := out.push last
        else if (a.splitOn ":").length == 2 && !isLiteral a then
          match a.splitOn ":" with
          | [n, k] =>
            let some k := k.toNat? | throw s!"unsupported child {a}"
            let t ← E.term (.atom n)
            for _ in [0:k] do out := out.push t
          | _ => throw s!"unsupported child {a}"
        else out := out.push (← E.term x)
      | _ => out := out.push (← E.term x)
    return .app f out.toList
  | x => .error s!"not a term: {repr x}"

/-- A pattern, or `none` for a construct the `Pat` type does not express. -/
partial def Env.pat (E : Env) : SExp → Option Pat
  | .atom a =>
    if isLiteral a then some (.lit a)
    else if a.startsWith ".." || a.startsWith ":" || (a.splitOn ":").length > 1 then none
    else match E.globals.lookup a with
      | some t => some (ofTerm t)
      | none => if E.ops.contains a then some (.app a []) else some (.var a)
  | .list (.atom f :: args) =>
    if f == "=" || !E.ops.contains f then none
    else (args.mapM E.pat).map (.app f)
  | _ => none
where
  ofTerm : Term → Pat
    | .lit v => .lit v
    | .app f args => .app f (args.map ofTerm)

/-- A body atom or guard: an equality, or a pattern that only asks for a term
to exist (no constraint in a model, whose operators are total). -/
def Env.guard (E : Env) : SExp → Option (List (Pat × Pat))
  | .list [.atom "=", p, q] => do return [(← E.pat p, ← E.pat q)]
  | x => (E.pat x).map fun _ => []

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

/-- The rules of a `rewrite`: `lhs` (whose root binding `(= v p)` becomes an
equality premise) to `rhs`, under the `:when` guards. -/
def Env.rewriteRules (E : Env) (lhs rhs : SExp) (tags : List SExp) : List Rule :=
  let (lhs, root) : SExp × List (Pat × Pat) :=
    match lhs with
    | .list [.atom "=", .atom v, p] =>
      (p, match E.pat p with
        | some pp => [(.var v, pp)]
        | none => [])
    | _ => (lhs, [])
  let guards : Option (List (Pat × Pat)) :=
    match tagArg ":when" tags with
    | some (.list gs) => (gs.mapM E.guard).map List.flatten
    | some _ => none
    | none => some []
  if tags.any (fun t => match t with | .atom ":let" => true | _ => false) then []
  else match E.pat lhs, E.pat rhs, guards with
    | some l, some r, some gs => [{ lhs := l, rhs := r, eqs := root ++ gs }]
    | _, _, _ => []

/-- The rules of a `rule`: one per `union` action, under the body's
equalities, with the action's `let` names expanded. -/
def Env.ruleRules (E : Env) (body actions : List SExp) : List Rule :=
  match (body.mapM E.guard).map List.flatten with
  | none => []
  | some eqs => go eqs actions []
where
  go (eqs : List (Pat × Pat)) : List SExp → List (String × Pat) → List Rule
    | .list [.atom "union", p, q] :: rest, lets =>
      match subst lets (E.pat p), subst lets (E.pat q) with
      | some l, some r => { lhs := l, rhs := r, eqs } :: go eqs rest lets
      | _, _ => go eqs rest lets
    | .list [.atom "let", .atom v, t] :: rest, lets =>
      match subst lets (E.pat t) with
      | some p => go eqs rest ((v, p) :: lets)
      | none => []
    | _ :: rest, lets => go eqs rest lets
    | [], _ => []
  subst (lets : List (String × Pat)) : Option Pat → Option Pat
    | some p => some (substP lets p)
    | none => none
  substP (lets : List (String × Pat)) : Pat → Pat
    | .var x => (lets.lookup x).getD (.var x)
    | .lit v => .lit v
    | .app f ps => .app f (ps.map (substP lets))

def declTags (xs : List SExp) : List SExp :=
  xs.dropWhile fun x => match x with | .atom a => !a.startsWith ":" | _ => true

/-- Reads one command. -/
def step (E : Env) (P : Program) (o : Nat) : SExp → Except String (Env × Program)
  | .list (.atom "function" :: .atom f :: _ :: _ :: tags)
  | .list (.atom "constructor" :: .atom f :: _ :: _ :: tags) => do
    let E := { E with ops := f :: E.ops }
    let kind := kindOf (atoms tags)
    let unit ← match identityOf tags with
      | some t => if kind == .assoc || kind == .ac || kind == .aci then some <$> E.term t else pure none
      | none => pure none
    return (E, { P with ops := P.ops ++ [{ name := f, kind, unit }] })
  | .list (.atom "relation" :: .atom f :: _) => return ({ E with ops := f :: E.ops }, P)
  | .list (.atom "datatype" :: _ :: variants) => do
    let mut E := E
    let mut P := P
    for v in variants do
      if let .list (.atom f :: rest) := v then
        E := { E with ops := f :: E.ops }
        let tags := declTags rest
        let kind := kindOf (atoms tags)
        let unit ← match identityOf tags with
          | some t => if kind == .assoc || kind == .ac || kind == .aci then some <$> E.term t else pure none
          | none => pure none
        P := { P with ops := P.ops ++ [{ name := f, kind, unit }] }
    return (E, P)
  | .list [.atom "let", .atom x, t] => do
    let t ← E.term t
    return ({ E with globals := (x, t) :: E.globals }, P)
  | .list [.atom "union", a, b] => do
    return (E, { P with decls := P.decls ++ [(o, .axiom (← E.term a) (← E.term b))] })
  | .list [.atom "check-eq", a, b]
  | .list [.atom "check", .list [.atom "=", a, b]] => do
    return (E, { P with decls := P.decls ++ [(o, .goal (← E.term a) (← E.term b))] })
  | .list (.atom "rewrite" :: l :: r :: tags) =>
    return (E, { P with decls := P.decls ++ [(o, .rules (E.rewriteRules l r tags))] })
  | .list (.atom "birewrite" :: l :: r :: tags) =>
    return (E, { P with decls := P.decls ++
      [(o, .rules (E.rewriteRules l r tags ++ E.rewriteRules r l tags))] })
  | .list (.atom "rule" :: .list body :: .list actions :: _) =>
    return (E, { P with decls := P.decls ++ [(o, .rules (E.ruleRules body actions))] })
  | .list (.atom "push" :: _) | .list (.atom "pop" :: _) | .list (.atom "include" :: _) =>
    .error "push, pop and include are not supported"
  | _ => return (E, P)

def parseProgram (src : String) : Except String Program := do
  let forms ← readTop src
  let mut E : Env := {}
  let mut P : Program := { ops := [], decls := [] }
  for (o, x) in forms do
    (E, P) ← step E P o x
  return P

/-! ## The certificate

```
semper-cert 1
n <id> a <op> <child>...
n <id> l <literal>
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
    | "n" :: i :: "l" :: _ =>
      unless (← nat i) == nodes.size do throw s!"node out of order: {l}"
      let pre := s!"n {i} l "
      nodes := nodes.push (.lit (l.drop pre.length).toString)
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

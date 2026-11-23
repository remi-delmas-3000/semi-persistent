import SemperCheck.Syntax

/-!
# Primitive operations on literals

The engine evaluates a primitive (`i64::+`, `String::concat`, ...) on literal
values (`egraph/src/model.rs`). This file states what each one computes:
`primOk f args out` holds when `f` applied to the literals `args` has the
literal `out` as its value. It is part of the statement of the soundness
theorem: a model interprets every primitive application to literals as the
literal `primOk` gives (`Semantics.lean`, `Models`).

A literal is a sort and a spelling. `Val.parse` reads its value; two spellings
of one value are one value here. Where the engine's operation has no value (an
overflow, a division by zero, an exponent out of range), `primEval` has none
either. Where this file is more cautious than the engine (a string spelled
with a backslash, a rational power with a large exponent), it gives no value:
`primOk` is then false, which constrains the models less, never more.

Assumptions about the engine's platform: `usize` is 64 bits wide.
-/

namespace SemperCheck

/-- The value of a literal. A rational is a reduced fraction with a positive
denominator. -/
inductive Val where
  | bool (b : Bool)
  | i64 (v : Int)
  | u64 (v : Nat)
  | usize (v : Nat)
  | ibig (v : Int)
  | ubig (v : Nat)
  | rbig (n : Int) (d : Nat)
  | f64 (x : Float)
  | str (s : String)
  deriving Inhabited

namespace Val

def minI64 : Int := -9223372036854775808
def maxI64 : Int := 9223372036854775807
def two64 : Nat := 18446744073709551616

/-- `v` as an `i64`, when it is in range. -/
def ofI64 (v : Int) : Option Val := if minI64 ≤ v ∧ v ≤ maxI64 then some (.i64 v) else none

/-- `v` wrapped into the `i64` range, two's complement. -/
def wrapI64 (v : Int) : Val := .i64 ((v - minI64).emod (two64 : Int) + minI64)

/-- `v` clamped to the `i64` range. -/
def satI64 (v : Int) : Val := .i64 (if v < minI64 then minI64 else if v > maxI64 then maxI64 else v)

/-- The reduced fraction `n / d`, for `d ≠ 0`. -/
def mkRat (n d : Int) : Option Val :=
  if d == 0 then none
  else
    let n := if d < 0 then -n else n
    let d := d.natAbs
    let g := Nat.gcd n.natAbs d
    if g == 0 then none else some (.rbig (n / (g : Int)) (d / g))

/-- Digits to a number. -/
def digits? (s : String) : Option Nat := if s.isEmpty then none else s.toNat?

/-- A decimal spelling of a float, as Rust's `str::parse::<f64>` reads it:
`[+-]digits[.digits][e[+-]digits]` with a digit somewhere, or `inf`,
`infinity`, `nan` in any case. The value is `Float.ofScientific`'s. -/
def parseFloat (s : String) : Option Float :=
  let (neg, body) :=
    if s.startsWith "-" then (true, (s.drop 1).toString)
    else if s.startsWith "+" then (false, (s.drop 1).toString)
    else (false, s)
  let sign (x : Float) : Float := if neg then -x else x
  let low := body.toLower
  if low == "inf" || low == "infinity" then some (sign (1.0 / 0.0))
  else if low == "nan" then some (0.0 / 0.0)
  else
    let (mant, exp) := match low.splitOn "e" with
      | [m] => (m, some (0 : Int))
      | [m, e] => (m, if e.startsWith "+" then (e.drop 1).toString.toInt? else e.toInt?)
      | _ => (low, none)
    let (ip, fp) := match mant.splitOn "." with
      | [i] => (i, some "")
      | [i, f] => (i, some f)
      | _ => (mant, none)
    match exp, fp with
    | some e, some fp =>
      if ip.isEmpty && fp.isEmpty then none
      else if !(ip ++ fp).all Char.isDigit then none
      else
        match (ip ++ fp).toNat? with
        | some m =>
          let e10 := e - (fp.length : Int)
          some (sign (if e10 < 0 then Float.ofScientific m true e10.natAbs
            else Float.ofScientific m false e10.natAbs))
        | none => none
    | _, _ => none

/-- The value of the literal `text` of sort `sort`. A string is spelled
between double quotes; one with a backslash has no value here, because the
program and the stream escape it differently. -/
def parse (sort text : String) : Option Val :=
  match sort with
  | "bool" => if text == "true" then some (.bool true) else if text == "false" then some (.bool false) else none
  | "i64" => text.toInt?.bind ofI64
  | "u64" => text.toNat?.bind fun v => if v < two64 then some (.u64 v) else none
  | "usize" => text.toNat?.bind fun v => if v < two64 then some (.usize v) else none
  | "IBig" => text.toInt?.map .ibig
  | "UBig" => text.toNat?.map .ubig
  | "RBig" =>
    match text.splitOn "/" with
    -- A whole rational is spelled without its denominator too.
    | [n] => n.toInt?.map fun n => .rbig n 1
    | [n, d] => match n.toInt?, d.toInt? with
      | some n, some d => mkRat n d
      | _, _ => none
    | _ => none
  | "f64" => (parseFloat text).map .f64
  | "String" =>
    if text.length ≥ 2 && text.startsWith "\"" && text.endsWith "\"" && !text.contains '\\' then
      some (.str ((text.drop 1).dropEnd 1).toString)
    else none
  | _ => none

/-- Two values are one value: floats as the engine orders them (every `NaN`
is one value, and `-0` is `0`). -/
def same : Val → Val → Bool
  | .bool a, .bool b => a == b
  | .i64 a, .i64 b => a == b
  | .u64 a, .u64 b => a == b
  | .usize a, .usize b => a == b
  | .ibig a, .ibig b => a == b
  | .ubig a, .ubig b => a == b
  | .rbig a b, .rbig c d => a == c && b == d
  | .f64 a, .f64 b => (a.isNaN && b.isNaN) || a == b
  | .str a, .str b => a == b
  | _, _ => false

end Val

open Val

/-- The engine's total order on floats: `NaN` is above every number. -/
def fLt (x y : Float) : Bool := if x.isNaN then false else if y.isNaN then true else x < y
def fEq (x y : Float) : Bool := (x.isNaN && y.isNaN) || x == y

/-- The six comparisons, from "less than" and "equal". -/
def cmp? (op : String) (lt eq : Bool) : Option Val :=
  match op with
  | "<" => some (.bool lt)
  | "<=" => some (.bool (lt || eq))
  | ">" => some (.bool (!lt && !eq))
  | ">=" => some (.bool !lt)
  | "==" => some (.bool eq)
  | "!=" => some (.bool !eq)
  | _ => none

/-- `a ^ e` when it is in the `i64` range: for `|a| ≥ 2` the result leaves the
range before `e` reaches 64. -/
def powI64 (a : Int) (e : Nat) : Option Val :=
  if a == 0 then ofI64 (if e == 0 then 1 else 0)
  else if a == 1 then ofI64 1
  else if a == -1 then ofI64 (if e % 2 == 0 then 1 else -1)
  else if e > 64 then none
  else ofI64 (a ^ e)

/-- Operations on `i64`: checked ones have no value on overflow. -/
def evalI64 (op : String) : List Val → Option Val
  | [.i64 a, .i64 b] =>
    match op with
    | "+" => ofI64 (a + b)
    | "-" => ofI64 (a - b)
    | "*" => ofI64 (a * b)
    | "/" => if b == 0 then none else ofI64 (a.tdiv b)
    | "%" => if b == 0 || (a == minI64 && b == -1) then none else ofI64 (a.tmod b)
    | "pow" => if 0 ≤ b ∧ b < 4294967296 then powI64 a b.toNat else none
    | "wrapping_add" => some (wrapI64 (a + b))
    | "wrapping_sub" => some (wrapI64 (a - b))
    | "wrapping_mul" => some (wrapI64 (a * b))
    | "saturating_add" => some (satI64 (a + b))
    | "saturating_sub" => some (satI64 (a - b))
    | "saturating_mul" => some (satI64 (a * b))
    | "min" => some (.i64 (if b < a then b else a))
    | "max" => some (.i64 (if a > b then a else b))
    | op => cmp? op (a < b) (a == b)
  | [.i64 a] =>
    match op with
    | "neg" => ofI64 (-a)
    | "abs" => ofI64 (if a < 0 then -a else a)
    | "wrapping_neg" => some (wrapI64 (-a))
    | "wrapping_abs" => some (wrapI64 (if a < 0 then -a else a))
    | "saturating_neg" => some (satI64 (-a))
    | "saturating_abs" => some (satI64 (if a < 0 then -a else a))
    | _ => none
  | _ => none

/-- Operations on a 64-bit unsigned sort, whose values `mk` wraps. -/
def evalU64 (mk : Nat → Val) (op : String) (a b : Nat) : Option Val :=
  let checked (v : Nat) : Option Val := if v < two64 then some (mk v) else none
  let sat (v : Nat) : Val := mk (if v < two64 then v else two64 - 1)
  match op with
  | "+" => checked (a + b)
  | "-" => if a < b then none else some (mk (a - b))
  | "*" => checked (a * b)
  | "/" => if b == 0 then none else some (mk (a / b))
  | "%" => if b == 0 then none else some (mk (a % b))
  | "wrapping_add" => some (mk ((a + b) % two64))
  | "wrapping_sub" => some (mk ((a + two64 - b) % two64))
  | "wrapping_mul" => some (mk ((a * b) % two64))
  | "saturating_add" => some (sat (a + b))
  | "saturating_sub" => some (mk (a - b))
  | "saturating_mul" => some (sat (a * b))
  | "min" => some (mk (min a b))
  | "max" => some (mk (max a b))
  | op => cmp? op (a < b) (a == b)

def evalF64 (op : String) : List Val → Option Val
  | [.f64 a, .f64 b] =>
    match op with
    | "+" => some (.f64 (a + b))
    | "-" => some (.f64 (a - b))
    | "*" => some (.f64 (a * b))
    | "/" => some (.f64 (a / b))
    | "min" => some (.f64 (if fLt b a then b else a))
    | "max" => some (.f64 (if fLt b a then a else b))
    | op => cmp? op (fLt a b) (fEq a b)
  | [.f64 a] =>
    match op with
    | "neg" => some (.f64 (-a))
    | "abs" => some (.f64 a.abs)
    | _ => none
  | _ => none

/-- The bytes `st .. en` of `s` as a string, when they are one: the two ends
are then on character boundaries, as Rust's `str::get` asks. -/
def byteSlice (s : String) (st en : Nat) : String :=
  let b := s.toUTF8
  if st ≤ en ∧ en ≤ b.size then (String.fromUTF8? (b.extract st en)).getD "" else ""

def evalStr (op : String) : List Val → Option Val
  | [.str a, .str b] =>
    match op with
    | "concat" => some (.str (a ++ b))
    | "contains" => some (.bool ((a.splitOn b).length > 1 || b.isEmpty))
    | "==" => some (.bool (a == b))
    | "!=" => some (.bool (a != b))
    | _ => none
  | [.str s, .str f, .str t] =>
    match op with
    -- The first occurrence only.
    | "replace" =>
      if f.isEmpty then some (.str (t ++ s))
      else match s.splitOn f with
        | [] | [_] => some (.str s)
        | x :: rest => some (.str (x ++ t ++ f.intercalate rest))
    | _ => none
  | [.str s] => if op == "len" then some (.usize s.utf8ByteSize) else none
  | [.str s, .usize st, .usize ln] =>
    if op == "substr" then some (.str (byteSlice s st (min (st + ln) s.utf8ByteSize))) else none
  | [.str s, .usize i] => if op == "at" then some (.str (byteSlice s i (i + 1))) else none
  | _ => none

def evalIBig (op : String) : List Val → Option Val
  | [.ibig a, .ibig b] =>
    match op with
    | "+" => some (.ibig (a + b))
    | "-" => some (.ibig (a - b))
    | "*" => some (.ibig (a * b))
    | "/" => if b == 0 then none else some (.ibig (a.tdiv b))
    | "%" => if b == 0 then none else some (.ibig (a.tmod b))
    | "min" => some (.ibig (min a b))
    | "max" => some (.ibig (max a b))
    | op => cmp? op (a < b) (a == b)
  | [.ibig a] =>
    match op with
    | "neg" => some (.ibig (-a))
    | "abs" => some (.ibig (if a < 0 then -a else a))
    | _ => none
  | _ => none

def evalUBig (op : String) : List Val → Option Val
  | [.ubig a, .ubig b] =>
    match op with
    | "+" => some (.ubig (a + b))
    | "-" => if a < b then none else some (.ubig (a - b))
    | "*" => some (.ubig (a * b))
    | "/" => if b == 0 then none else some (.ubig (a / b))
    | "%" => if b == 0 then none else some (.ubig (a % b))
    | "min" => some (.ubig (min a b))
    | "max" => some (.ubig (max a b))
    | op => cmp? op (a < b) (a == b)
  | _ => none

def evalRBig (op : String) : List Val → Option Val
  | [.rbig a b, .rbig c d] =>
    let lt : Bool := a * (d : Int) < c * (b : Int)
    let eq : Bool := a == c && b == d
    match op with
    | "+" => mkRat (a * d + c * b) (b * d)
    | "-" => mkRat (a * d - c * b) (b * d)
    | "*" => mkRat (a * c) (b * d)
    | "/" => if c == 0 then none else mkRat (a * d) (b * c)
    | "min" => some (if lt then .rbig a b else .rbig c d)
    | "max" => some (if lt then .rbig c d else .rbig a b)
    | op => cmp? op lt eq
  | [.rbig a b] =>
    match op with
    | "neg" => some (.rbig (-a) b)
    | "abs" => some (.rbig (if a < 0 then -a else a) b)
    | _ => none
  | [.i64 k] => if op == "from_int" then some (.rbig k 1) else none
  | [.rbig a b, .i64 k] =>
    match op with
    | "scale" => mkRat (a * k) b
    -- A non-negative exponent that fits `i32`; a large one has no value here.
    | "pow" => if 0 ≤ k ∧ k ≤ 4096 then mkRat (a ^ k.toNat) ((b : Int) ^ k.toNat) else none
    | _ => none
  | _ => none

/-- The value of primitive `f` on the values `args`, as the engine computes
it (`egraph/src/model.rs`). -/
def primEval (f : String) (args : List Val) : Option Val :=
  match f, args with
  | "and", [.bool a, .bool b] => some (.bool (a && b))
  | "or", [.bool a, .bool b] => some (.bool (a || b))
  | "not", [.bool a] => some (.bool !a)
  | _, _ =>
    match f.splitOn "::" with
    | [sort, op] =>
      -- `S::if c x y`, for every sort.
      if op == "if" then
        match args with
        | [.bool c, x, y] => some (if c then x else y)
        | _ => none
      else
        match sort with
        | "i64" => evalI64 op args
        | "u64" => match args with
          | [.u64 a, .u64 b] => evalU64 .u64 op a b
          | _ => none
        | "usize" => match args with
          | [.usize a, .usize b] => evalU64 .usize op a b
          | _ => none
        | "f64" => evalF64 op args
        | "String" => evalStr op args
        | "IBig" => evalIBig op args
        | "UBig" => evalUBig op args
        | "RBig" => evalRBig op args
        | _ => none
    | _ => none

/-- Primitive `f` applied to the literals `args` (sort and spelling each) has
the literal `out` as its value. -/
def primOk (f : String) (args : List (String × String)) (out : String × String) : Bool :=
  match args.mapM (fun a => Val.parse a.1 a.2), Val.parse out.1 out.2 with
  | some vs, some o => match primEval f vs with
    | some v => v.same o
    | none => false
  | _, _ => false

/-- The argument sorts and the result sort of a primitive. -/
def primSig (f : String) : Option (List String × String) :=
  match f with
  | "and" | "or" => some (["bool", "bool"], "bool")
  | "not" => some (["bool"], "bool")
  | "RBig::from_int" => some (["i64"], "RBig")
  | "RBig::scale" | "RBig::pow" => some (["RBig", "i64"], "RBig")
  | "String::concat" => some (["String", "String"], "String")
  | "String::contains" | "String::==" | "String::!=" => some (["String", "String"], "bool")
  | "String::replace" => some (["String", "String", "String"], "String")
  | "String::len" => some (["String"], "usize")
  | "String::substr" => some (["String", "usize", "usize"], "String")
  | "String::at" => some (["String", "usize"], "String")
  | _ =>
    match f.splitOn "::" with
    | [s, op] =>
      if !["bool", "i64", "u64", "usize", "f64", "String", "IBig", "UBig", "RBig"].contains s then none
      else if op == "if" then some (["bool", s, s], s)
      else if ["<", "<=", ">", ">=", "==", "!="].contains op then
        if s == "bool" then none else some ([s, s], "bool")
      else if ["neg", "abs", "wrapping_neg", "wrapping_abs", "saturating_neg", "saturating_abs"].contains op then
        if ["i64", "f64", "IBig", "RBig"].contains s then some ([s], s) else none
      else if ["+", "-", "*", "/", "%", "pow", "min", "max", "wrapping_add", "wrapping_sub",
          "wrapping_mul", "saturating_add", "saturating_sub", "saturating_mul"].contains op then
        if s == "bool" || s == "String" then none else some ([s, s], s)
      else none
    | _ => none

/-- A spelling of a value, for the literal a nested primitive evaluates to. -/
def Val.spell : Val → Option String
  | .bool true => some "true"
  | .bool false => some "false"
  | .i64 v => some (toString v)
  | .u64 v => some (toString v)
  | .usize v => some (toString v)
  | .ibig v => some (toString v)
  | .ubig v => some (toString v)
  | .rbig n d => some (if d == 1 then toString n else s!"{n}/{d}")
  | .str t => if t.contains '\\' || t.contains '"' then none else some s!"\"{t}\""
  -- The exact value `m * 2^e`, as an integer or as `m * 5^k` with exponent `-k`.
  | .f64 x =>
    if x.isNaN then some "NaN"
    else if x.isInf then some (if x < 0 then "-inf" else "inf")
    else if x == 0 then some (if 1.0 / x < 0 then "-0" else "0")
    else
      -- `|x| = f * 2^e` with `f` in `[1/2, 1)`, so `f * 2^53` is a whole number.
      let (f, e) := x.abs.frExp
      let m : Nat := (f * 9007199254740992.0).toUInt64.toNat
      let e : Int := e - 53
      let sign := if x < 0 then "-" else ""
      if e ≥ 0 then some s!"{sign}{m * 2 ^ e.toNat}"
      else some s!"{sign}{m * 5 ^ e.natAbs}e-{e.natAbs}"

end SemperCheck

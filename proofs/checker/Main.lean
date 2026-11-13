import SemperCheck

/-!
`semper-check PROGRAM.egg CERT`: checks every step of the certificate against
the program, then reports, for each `check-eq` of the program, whether the
certificate proves it (`goal_sound` states what a proved goal means). Exits 0
when every step checks and every `check-eq` is proved, 1 when a step fails or
a `check-eq` is unproved, 2 when an input does not parse.
-/

open SemperCheck

def main (args : List String) : IO UInt32 := do
  let [progPath, certPath] := args
    | IO.eprintln "usage: semper-check PROGRAM.egg CERT"; return 2
  let P ← match parseProgram (← IO.FS.readFile progPath) with
    | .ok P => pure P
    | .error e => IO.eprintln s!"program: {e}"; return 2
  let cert ← match parseCert (← IO.FS.readFile certPath) with
    | .ok c => pure c
    | .error e => IO.eprintln s!"certificate: {e}"; return 2
  let some (C, acc) := runCert P cert
    | if !wfNodes cert.nodes then
        IO.eprintln "certificate rejected: a node has a child at or after it"
      else
        let C := mkCtx P cert
        let mut acc : Array Concl := #[]
        for st in cert.steps do
          match C.checkStep acc st with
          | some c => acc := acc.push c
          | none => IO.eprintln s!"certificate rejected: step {acc.size} fails: {repr st}"; break
      return 1
  let mut proved := 0
  let mut total := 0
  for (o, d) in P.decls do
    if let .goal l r := d then
      total := total + 1
      if C.checkGoal acc cert.goals o l r then proved := proved + 1
      else IO.println s!"unproved: check-eq at byte {o}"
  IO.println s!"{cert.steps.size} steps checked; {proved} of {total} check-eq proved"
  return if proved == total then 0 else 1

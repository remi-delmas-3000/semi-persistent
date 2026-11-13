import SemperCheck

/-!
`semper-check PROGRAM.egg CERT`: checks every step of the certificate against
the program, then reports, for each `check-eq` of the program, whether the
certificate proves it (`goal_sound` states what a proved goal means). A step
that does not check is reported and concludes only `0 = 0`, so it costs the
goals that depend on it and no others. Exits 0 when every step checks and
every `check-eq` is proved, 1 when a step fails or a `check-eq` is unproved, 2
when an input does not parse.
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
    | IO.eprintln "certificate rejected: a node has a child at or after it"; return 1
  -- A step that does not check concludes `0 = 0` (`Ctx.failed`); report each.
  let mut failures := 0
  let mut seen : Array Concl := #[]
  for st in cert.steps do
    if (C.checkStep seen st).isNone then
      failures := failures + 1
      if failures ≤ 5 then IO.eprintln s!"step {seen.size} fails: {repr st}"
    seen := seen.push (acc[seen.size]!)
  let mut proved := 0
  let mut total := 0
  for (o, d) in P.decls do
    if let .goal l r := d then
      total := total + 1
      if C.checkGoal acc cert.goals o l r then proved := proved + 1
      else IO.println s!"unproved: check-eq at byte {o}"
  IO.println s!"{cert.steps.size} steps checked, {failures} failed; {proved} of {total} check-eq proved"
  return if proved == total && failures == 0 then 0 else 1

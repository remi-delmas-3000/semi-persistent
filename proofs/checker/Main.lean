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

/-- `semper-check --replay PROGRAM.egg TRACE`: replays the engine's event
stream (`REPLAY.md`). Not covered by a soundness theorem yet. -/
def replay (progPath tracePath : String) : IO UInt32 := do
  let P ← match parseProgram (← IO.FS.readFile progPath) with
    | .ok P => pure P
    | .error e => IO.eprintln s!"program: {e}"; return 2
  let h ← IO.FS.Handle.mk tracePath .read
  let mut S := Replay.start P
  if (← IO.getEnv "SEMPER_REPLAY_ASSUME").isSome then
    S := { S with assume := true }
    IO.eprintln "measurement mode: unchecked merges are applied; proved counts are not proofs"
  -- `SEMPER_REPLAY_SHOW=n` prints the first `n` failed lines.
  let shown := ((← IO.getEnv "SEMPER_REPLAY_SHOW").bind (·.toNat?)).getD 0
  repeat
    let line ← h.getLine
    if line.isEmpty then break
    let beforeU := S.nUnjustified
    let before := S.nFailed
    S := Replay.step S ((line.splitOn "\n").headD "")
    if S.nUnjustified > beforeU && beforeU < shown then IO.eprintln s!"no kernel step at event {S.events}: {line}"
    if S.nFailed > before && S.nFailed ≤ shown then IO.eprintln s!"failed event {S.events} [{S.lastCause}]: {line}"
  let total := (P.decls.filter fun (_, d) => match d with | .goal .. => true | _ => false).length
  let proved := (P.decls.filter fun (o, d) =>
    match d with | .goal .. => S.proved.contains o | _ => false).length
  let nFailed := S.nFailed
  let nUnchecked := S.unchecked.fold (fun n _ k => n + k) 0
  for (c, k) in S.failed.toList do IO.println s!"failed: {k} {c}"
  for (c, k) in S.unchecked.toList do IO.println s!"unchecked: {k} {c}"
  for (c, k) in S.unjustified.toList do IO.println s!"no kernel step: {k} {c}"
  -- The kernel checks the steps the replay emitted.
  let cert := Replay.certOf S
  let nSteps := cert.steps.size
  if (runCert P cert).isNone then IO.println "kernel: the node table is rejected"
  -- `Replay.replay_sound` is about exactly these.
  let kernel := (Replay.provedBy P cert).length
  IO.println s!"kernel: {nSteps} steps, {kernel} of {total} check-eq proved"
  IO.println s!"{S.events} events replayed, {nFailed} failed, {nUnchecked} unchecked; {proved} of {total} check-eq proved"
  return if proved == total && nFailed == 0 && nUnchecked == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  if let ["--replay", progPath, tracePath] := args then return ← replay progPath tracePath
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
        IO.eprintln "certificate rejected: a node is ill-sorted"
      return 1
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

import SemperCheck
import Std.Data.HashSet

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
stream (`REPLAY.md`) line by line with `Replay.step`. The `check-eq` reported
as proved are the ones `Replay.replay_sound` is about. -/
def replay (progPath tracePath : String) : IO UInt32 := do
  let (P, skipped) ← match parseProgramWhy (← IO.FS.readFile progPath) with
    | .ok r => pure r
    | .error e => IO.eprintln s!"program: {e}"; return 2
  let h ← IO.FS.Handle.mk tracePath .read
  -- The cause of the first event that fails, has no witness or gets no kernel
  -- step: the later ones of a program can follow from it.
  let mut first : Option String := none
  let mut S := Replay.start P
  -- `SEMPER_REPLAY_SHOW=n` prints the first `n` failed lines.
  let shown := ((← IO.getEnv "SEMPER_REPLAY_SHOW").bind (·.toNat?)).getD 0
  let nodes := (← IO.getEnv "SEMPER_REPLAY_NODES").isSome
  -- `SEMPER_REPLAY_FAILED=FILE` lists every failed event: number, cause, line.
  let failedOut ← IO.getEnv "SEMPER_REPLAY_FAILED"
  if failedOut.isSome then S := { S with logFailed := true }
  repeat
    let line ← h.getLine
    if line.isEmpty then break
    let beforeU := S.nUnjustified
    let before := S.nFailed
    let beforeR := S.core.rejected
    let beforeN := S.unchecked.fold (fun n _ k => n + k) 0
    S := Replay.step S ((line.splitOn "\n").headD "")
    if S.nUnjustified > beforeU && beforeU < shown then IO.eprintln s!"no kernel step at event {S.events}: {line}"
    if S.nFailed > before && S.nFailed ≤ shown then IO.eprintln s!"failed event {S.events} [{S.lastCause}]: {line}"
    -- With `SEMPER_REPLAY_NODES`, each node the failed line names: its table
    -- id, its class's root and its definition.
    if S.nFailed > before && S.nFailed ≤ shown && nodes then
      for x in ((line.splitOn "\n").headD "").splitOn " " do
        if let some t := S.node? x then
          let d := match S.defOf t with
            | some (.app f cs) => s!"{f} {cs}"
            | some (.lit s v) => s!"{s} {v}"
            | none => "?"
          IO.eprintln s!"  {x}: table {t}, root {S.fd t}, {d}"
    if first.isNone then
      let kind := (line.splitOn " ").headD ""
      if S.nFailed > before then
        let parts := S.lastCause.splitOn " | "
        let cause := parts.headD ""
        -- A rule the reader did not read: its reason.
        let why := if cause == "rule: outside the reader's language" then
            match ((parts.getD 1 "").splitOn " ").map (·.toNat?) with
            | [some o, some j] =>
              (skipped.find? fun (o', j', _) => o' == o && j' == j).map fun (_, _, e) => e
            | _ => none
          else none
        first := some (match why with
          | some e => s!"unread rule: {e}"
          | none => cause)
      else if S.unchecked.fold (fun n _ k => n + k) 0 > beforeN then
        first := some s!"no witness: {((line.splitOn " ").getD 1 "").trimAscii}"
      else if S.nUnjustified > beforeU then
        first := some s!"no kernel steps: {kind} line"
    if S.core.rejected > beforeR && beforeR < shown then IO.eprintln s!"kernel rejects a step at event {S.events}: {line}"
  if let some f := failedOut then IO.FS.writeFile f (String.join S.failedLog.toList)
  let total := (P.decls.filter fun (_, d) => match d with | .goal .. => true | _ => false).length
  let joined := (P.decls.filter fun (o, d) =>
    match d with | .goal .. => S.proved.contains o | _ => false).length
  let nFailed := S.nFailed
  let nUnchecked := S.unchecked.fold (fun n _ k => n + k) 0
  if let some c := first then IO.println s!"first: {c}"
  for (c, k) in (skipped.foldl (fun (m : Std.HashMap String Nat) (_, _, e) => m.insert e (m.getD e 0 + 1)) {}).toList do
    IO.println s!"unread rule: {k} {c}"
  for (c, k) in S.failed.toList do IO.println s!"failed: {k} {c}"
  for (c, k) in S.unchecked.toList do IO.println s!"unchecked: {k} {c}"
  for (c, k) in S.unjustified.toList do IO.println s!"no kernel step: {k} {c}"
  -- The steps the replayer built that the kernel does not accept: each
  -- concludes only `0 = 0`, and none should exist.
  IO.println s!"kernel: {S.core.rejected} steps rejected"
  -- `Replay.replay_sound` is about exactly these.
  let got : Std.HashSet Nat := S.core.goals.foldl (fun m g => m.insert g.1) {}
  let kernel := (P.decls.filter fun (o, d) =>
    match d with | .goal .. => got.contains o | _ => false).length
  IO.println s!"kernel: {S.core.acc.size} steps, {kernel} of {total} check-eq proved"
  if shown > 0 then
    for (o, d) in P.decls do
      if let .goal .. := d then
        if !got.contains o then IO.eprintln s!"kernel: check-eq at byte {o} not proved"
  IO.println s!"{S.events} events replayed, {nFailed} failed, {nUnchecked} unchecked; {joined} of {total} check-eq in one class"
  return if kernel == total && nFailed == 0 && nUnchecked == 0 then 0 else 1

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

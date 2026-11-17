import SemperCheck.Replay
import SemperCheck.Sound

/-!
# What a replayed `check-eq` means

The replayer (`Replay.lean`) is not trusted. Whatever it reads, it ends with a
node table, a list of kernel steps and, for each `check-eq` it joined, the
step that should prove it. `provedBy` runs the kernel (`Kernel.lean`) on that
certificate and keeps the `check-eq` the kernel accepts; `semper-check
--replay` reports exactly their number. `replay_sound` is `goal_sound` for
them: a kept `check-eq` holds in every model of the commands before it.

The statement does not mention the stream or the replayer's state: no property
of either is assumed. A wrong check in the replayer, or a wrong line in the
stream, yields a step the kernel rejects.
-/

namespace SemperCheck.Replay

/-- The certificate a replay ends with. -/
def certOf (S : St) : Cert :=
  { nodes := S.defs.map fun d =>
      match d with
      | some (.app f cs) => Node.app f cs
      | some (.lit s v) => Node.lit s v
      | none => Node.lit "" "",
    steps := S.steps,
    goals := S.goalSteps }

/-- The `check-eq` of `P`, each with its offset, that the kernel accepts from
`cert`. -/
def provedBy (P : Program) (cert : Cert) : List (Nat × Term × Term) :=
  match runCert P cert with
  | some (C, acc) =>
    P.decls.filterMap fun (od : Nat × Decl) =>
      match od.2 with
      | Decl.goal l r => if C.checkGoal acc cert.goals od.1 l r then some (od.1, l, r) else none
      | _ => none
  | none => []

/-- The `check-eq` the replay of `lines` against `P` proves. -/
def proved (P : Program) (lines : List String) : List (Nat × Term × Term) :=
  provedBy P (certOf (lines.foldl step (start P)))

/-- A `check-eq` the kernel accepts from any certificate holds in every model
of the commands before it. -/
theorem provedBy_sound {P : Program} {cert : Cert} {o : Nat} {l r : Term}
    (h : (o, l, r) ∈ provedBy P cert) (M : Model) (hM : M.Models P o) : M.eval l = M.eval r := by
  unfold provedBy at h
  split at h
  · rename_i C acc hrun
    obtain ⟨od, -, hod⟩ := List.mem_filterMap.1 h
    split at hod
    · rename_i l' r' hd
      split at hod
      · rename_i hg
        simp only [Option.some.injEq, Prod.mk.injEq] at hod
        obtain ⟨rfl, rfl, rfl⟩ := hod
        exact goal_sound hrun hg M hM
      · cases hod
    · cases hod
  · simp at h

/-- A `check-eq` the replay of a stream proves holds in every model of the
commands before it, whatever the stream is. -/
theorem replay_sound {P : Program} {lines : List String} {o : Nat} {l r : Term}
    (h : (o, l, r) ∈ proved P lines) (M : Model) (hM : M.Models P o) : M.eval l = M.eval r :=
  provedBy_sound h M hM

end SemperCheck.Replay

#print axioms SemperCheck.Replay.replay_sound

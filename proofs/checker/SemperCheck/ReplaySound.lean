import SemperCheck.Replay

/-!
# What a replay proves

`replay P lines` is the replayer's state after the stream `lines`, read
against the program `P`: `semper-check --replay` computes it line by line with
the same `step`. Its checked part is a `Core P` (`Core.lean`), which only
proved operations build, so the invariant of `Core.lean` holds of the state
after every event, whatever the stream is and whatever the rest of the
replayer does:

* `step_classes`, `replay_classes`: two nodes the replayer holds in one class
  have one value in every model of the program. An event's check joins two
  classes only by a link that a kernel-checked step proves, so each event
  preserves this, the idempotent, nilpotent, inverse and cancellation events
  included: their steps are the kernel's `cong`, `nil`, `inv` and `cancel`.
* `replay_sound`: a `check-eq` the replay reports as proved holds in every
  model of the commands before it.

No hypothesis mentions the stream: a wrong line yields a step the kernel
rejects, and the merge it was for is not applied.
-/

namespace SemperCheck.Replay

/-- The replayer's state after the stream `lines`. -/
def replay (P : Program) (lines : List String) : St P := lines.foldl step (start P)

/-- The `check-eq` of `P`, each with its offset, that the replay of `lines`
proves. -/
def proved (P : Program) (lines : List String) : List (Nat × Term × Term) :=
  (replay P lines).core.goals

/-- After one event, on any state: two nodes of one class have one value in
every model of the program. -/
theorem step_classes {P : Program} (S : St P) (line : String) {a b : Nat}
    (h : (step S line).fd a = (step S line).fd b) (M : Model) (hM : ∀ p, M.Models P p) :
    nval M (step S line).defs a = nval M (step S line).defs b :=
  (step S line).core.class_sound h M hM

/-- After any stream: two nodes of one class have one value in every model of
the program. -/
theorem replay_classes {P : Program} (lines : List String) {a b : Nat}
    (h : (replay P lines).fd a = (replay P lines).fd b) (M : Model) (hM : ∀ p, M.Models P p) :
    nval M (replay P lines).defs a = nval M (replay P lines).defs b :=
  (replay P lines).core.class_sound h M hM

/-- After one event, on any state: every `check-eq` recorded as proved holds
in every model of the commands before it. -/
theorem step_goals {P : Program} (S : St P) (line : String) {o : Nat} {l r : Term}
    (h : (o, l, r) ∈ (step S line).core.goals) (M : Model) (hM : M.Models P o) :
    M.eval l = M.eval r :=
  (step S line).core.goal_sound h M hM

/-- **Soundness of the replay.** A `check-eq` the replay of a stream proves
holds in every model of the commands before it, whatever the stream is. -/
theorem replay_sound {P : Program} {lines : List String} {o : Nat} {l r : Term}
    (h : (o, l, r) ∈ proved P lines) (M : Model) (hM : M.Models P o) : M.eval l = M.eval r :=
  (replay P lines).core.goal_sound h M hM

end SemperCheck.Replay

#print axioms SemperCheck.Replay.replay_sound
#print axioms SemperCheck.Replay.replay_classes

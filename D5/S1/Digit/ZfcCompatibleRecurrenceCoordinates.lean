/- GID: D5/S1/Digit/ZfcCompatibleRecurrenceCoordinates
   generality: G
   mirror-B: D5/B/S1/Digit/ZfcCompatibleRecurrenceCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every Fibonacci recurrence observation has two integer coordinates, with an explicit reconstruction formula. -/

import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S1.Digit.ZfcCompatibleRecurrenceCoordinates

variable {A : Type*} [AddCommGroup A]

def goldenWeight : Nat → Nat
  | 0 => 1
  | 1 => 2
  | n + 2 => goldenWeight (n + 1) + goldenWeight n

def companionWeight : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => companionWeight (n + 1) + companionWeight n

/-- The two initial coordinates reconstruct every sequence obeying the Fibonacci rule. -/
theorem recurrence_two_coordinate_reconstruction
    (w : Nat → A)
    (hrec : ∀ n, w (n + 2) = w (n + 1) + w n) :
    ∀ n, w n =
      (goldenWeight n : Nat) • (w 1 - w 0) +
        (companionWeight n : Nat) • (2 • w 0 - w 1) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [goldenWeight, companionWeight]
      abel
  | one =>
      simp [goldenWeight, companionWeight]
      abel
  | more n ih0 ih1 =>
      rw [hrec n, ih1, ih0]
      simp only [goldenWeight, companionWeight, add_nsmul]
      abel

end D5.S1.Digit.ZfcCompatibleRecurrenceCoordinates

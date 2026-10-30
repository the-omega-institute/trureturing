/- GID: D5/S1/Digit/Admissibility/CarrylessThirteenElevenContainment
   generality: I
   mirror-B: D5/B/S1/Digit/Admissibility/CarrylessThirteenElevenContainment
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise, mathlib/module/Mathlib.Data.Nat.EvenOddRec]
   utility: kind=checker; basis=terminal=gid:D5/S1/Digit/Admissibility/CarrylessThirteenElevenContainment.result; instance=D5/S1/Digit/Admissibility/CarrylessThirteenElevenContainment.related; result=D5/S1/Digit/Admissibility/CarrylessThirteenElevenContainment.result
   digest: The carryless-multiplier equation for 13 and 29 implies the equation for 11 and 31. -/

import D5.S1.Digit.Admissibility.CarrylessMultiplierEquivalence

/-! # Carryless multiplier containment -/

set_option autoImplicit false

namespace D5.S1.Digit.Admissibility.CarrylessThirteenElevenContainment

open CarrylessMultiplierEquivalence

private def related : Finset (State × State) := {
  (some (0, 0), some (0, 0)),
  (some (6, 14), some (5, 15)),
  (some (3, 7), some (2, 7)),
  (some (9, 9), some (8, 8)),
  (some (1, 3), none),
  (some (8, 13), none),
  (some (4, 4), some (4, 4)),
  (some (11, 10), some (9, 11)),
  (some (0, 1), none),
  (some (7, 15), none),
  (none, none),
  (some (2, 2), some (2, 2)),
  (some (8, 12), some (7, 13)),
  (none, some (4, 5)),
  (none, some (10, 10)),
  (some (3, 7), none),
  (some (10, 9), none),
  (some (1, 1), some (1, 1)),
  (some (7, 15), some (6, 14)),
  (some (4, 6), some (3, 6)),
  (some (10, 8), some (9, 9)),
  (none, some (5, 5)),
  (some (7, 14), some (6, 15)),
  (some (3, 7), some (3, 7)),
  (some (10, 9), some (8, 8)),
  (some (2, 3), none),
  (some (5, 4), some (4, 4)),
  (some (11, 10), some (10, 11)),
  (none, some (2, 2)),
  (none, some (8, 13)),
  (some (1, 3), some (1, 3)),
  (some (8, 13), some (7, 12)),
  (none, some (4, 4)),
  (none, some (9, 11)),
  (none, some (7, 13)),
  (none, some (1, 1)),
  (none, some (6, 14)),
  (some (0, 1), some (0, 1)),
  (none, some (3, 6)),
  (none, some (9, 9)),
  (none, some (0, 0)),
  (none, some (6, 15)),
  (none, some (3, 7)),
  (none, some (8, 8)),
  (none, some (10, 11)),
  (none, some (5, 15)),
  (none, some (1, 3)),
  (none, some (7, 12)),
  (none, some (2, 7)),
  (none, some (0, 1))
}

private theorem related_initial : (some (0, 0), some (0, 0)) ∈ related := by
  decide

private theorem related_terminal : ∀ p ∈ related,
    holds 29 13 p.1 0 → holds 31 11 p.2 0 := by
  decide

private theorem related_step : ∀ p ∈ related, ∀ b : Bool,
    (step 29 13 p.1 b, step 31 11 p.2 b) ∈ related := by
  decide

private theorem related_implication (k : ℕ) : ∀ p ∈ related,
    holds 29 13 p.1 k → holds 31 11 p.2 k := by
  induction k using Nat.evenOddRec with
  | h0 => exact related_terminal
  | h_even n ih =>
    intro p hp h
    have h₁ := (holds_step 29 13 p.1 false n).mp h
    have h₂ := ih _ (related_step p hp false) h₁
    exact (holds_step 31 11 p.2 false n).mpr h₂
  | h_odd n ih =>
    intro p hp h
    have h₁ := (holds_step 29 13 p.1 true n).mp h
    have h₂ := ih _ (related_step p hp true) h₁
    exact (holds_step 31 11 p.2 true n).mpr h₂

/-- The exact A115805-to-A115803 containment implication, for every natural input. -/
theorem result (k : ℕ) :
    13*k = carryless 29 k → 11*k = carryless 31 k := by
  intro hk
  simp only [carryless_eq] at hk ⊢
  have hk' : holds 29 13 (some (0, 0)) k := by
    simpa [holds] using hk
  have h := related_implication k (some (0, 0), some (0, 0)) related_initial hk'
  simpa [holds] using h

#print axioms result

end D5.S1.Digit.Admissibility.CarrylessThirteenElevenContainment

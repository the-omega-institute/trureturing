/- GID: D5/S1/Digit/Admissibility/CarrylessSevenFiveEquivalence
   generality: G
   mirror-B: D5/B/S1/Digit/Admissibility/CarrylessSevenFiveEquivalence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.EvenOddRec]
   utility: kind=checker; basis=terminal=gid:D5/S1/Digit/Admissibility/CarrylessSevenFiveEquivalence.result; instance=D5/S1/Digit/Admissibility/CarrylessSevenFiveEquivalence.related; result=D5/S1/Digit/Admissibility/CarrylessSevenFiveEquivalence.result
   digest: The carryless multiplier equations with ordinary multipliers seven and five are equivalent. -/
import D5.S1.Digit.Admissibility.CarrylessMultiplierEquivalence

/-! # Seven and five versus binary carryless multiplication -/

namespace D5.S1.Digit.Admissibility.CarrylessSevenFiveEquivalence

open CarrylessMultiplierEquivalence

private def related : Finset (State × State) := {
  (some (0, 0), some (0, 0)),
  (some (3, 5), some (2, 6)),
  (some (1, 2), some (1, 3)),
  (some (5, 7), some (3, 5)),
  (none, some (0, 1)),
  (none, some (3, 7)),
  (some (2, 3), some (1, 2)),
  (some (6, 6), some (4, 4)),
  (none, none),
  (none, some (1, 3)),
  (none, some (4, 5)),
  (some (3, 3), some (2, 2)),
  (some (1, 1), some (1, 1)),
  (some (5, 4), some (3, 7)),
  (some (4, 5), some (3, 6))
}

private theorem related_final : ∀ p ∈ related,
    holds 11 7 p.1 0 ↔ holds 13 5 p.2 0 := by
  decide

private theorem related_step : ∀ p ∈ related, ∀ b : Bool,
    (step 11 7 p.1 b, step 13 5 p.2 b) ∈ related := by
  decide

private theorem related_equiv (k : ℕ) : ∀ p ∈ related,
    holds 11 7 p.1 k ↔ holds 13 5 p.2 k := by
  induction k using Nat.evenOddRec with
  | h0 => exact related_final
  | h_even n ih =>
    intro p hp
    simpa using (holds_step 11 7 p.1 false n).trans
      ((ih _ (related_step p hp false)).trans (holds_step 13 5 p.2 false n).symm)
  | h_odd n ih =>
    intro p hp
    simpa using (holds_step 11 7 p.1 true n).trans
      ((ih _ (related_step p hp true)).trans (holds_step 13 5 p.2 true n).symm)

/-- The two equations specify the same natural numbers, including zero. -/
theorem result (k : ℕ) :
    7*k = carryless 11 k ↔ 5*k = carryless 13 k := by
  simp only [carryless_eq]
  have h := related_equiv k (some (0,0), some (0,0)) (by decide)
  simpa [holds] using h

#check @result
#print axioms result

end D5.S1.Digit.Admissibility.CarrylessSevenFiveEquivalence

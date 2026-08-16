/- GID: D5/S1/Depth/ContinuedFractions/GaussInverseStep
   generality: G
   mirror-B: D5/B/S1/Depth/ContinuedFractions/GaussInverseStep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A Gauss history coordinate recovers the partial quotient that produced it. -/

import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace D5.S1.Depth.ContinuedFractions.GaussInverseStep

/-- If `y` is a valid history coordinate and its next value is `1 / (a + y)`, then taking
the floor of the reciprocal of that next value recovers the partial quotient `a`. -/
theorem gauss_inverse_step_recovers_quotient (a : ℕ) {y : ℝ}
    (hy : y ∈ Set.Ico 0 1) :
    ⌊1 / (1 / ((a : ℝ) + y))⌋ = (a : ℤ) := by
  calc
    ⌊1 / (1 / ((a : ℝ) + y))⌋ = ⌊(a : ℝ) + y⌋ := by simp only [one_div, inv_inv]
    _ = (a : ℤ) + ⌊y⌋ := Int.floor_natCast_add a y
    _ = (a : ℤ) := by rw [Int.floor_eq_zero_iff.mpr hy, add_zero]

#print axioms gauss_inverse_step_recovers_quotient

end D5.S1.Depth.ContinuedFractions.GaussInverseStep

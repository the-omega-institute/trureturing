/- GID: D5/S3/Constants/Moments/GoldenWindowMoment
   generality: I
   mirror-B: D5/B/S3/Constants/Moments/GoldenWindowMoment
   mirror-E: none(waiver:exact-algebraic-identity-only)
   anchors: []
   digest: Evaluate every power moment of the uniform golden window in closed form. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S3.Constants.Moments.GoldenWindowMoment

open scoped goldenRatio

/-- Translating the golden window `[-phi, phi^-1]` by one turns its endpoints into
`[-phi^-1, phi]`, so every natural power moment has the displayed Binet form. -/
theorem golden_window_moment (j : Nat) :
    (∫ x in -φ..φ⁻¹, (1 + x) ^ j) =
      (φ ^ (j + 1) - (-φ⁻¹) ^ (j + 1)) / (j + 1) := by
  have hleft : -φ + 1 = -φ⁻¹ := by
    rw [Real.inv_goldenRatio]
    linarith [Real.one_sub_goldenConj]
  have hright : φ⁻¹ + 1 = φ := by
    rw [Real.inv_goldenRatio]
    linarith [Real.one_sub_goldenRatio]
  calc
    (∫ x in -φ..φ⁻¹, (1 + x) ^ j) = ∫ x in -φ..φ⁻¹, (x + 1) ^ j := by
      congr 1
      funext x
      rw [add_comm]
    _ = ∫ x in -φ + 1..φ⁻¹ + 1, x ^ j :=
      intervalIntegral.integral_comp_add_right (fun x : ℝ => x ^ j) 1
    _ = (φ ^ (j + 1) - (-φ⁻¹) ^ (j + 1)) / (j + 1) := by
      rw [hleft, hright, integral_pow]

end D5.S3.Constants.Moments.GoldenWindowMoment

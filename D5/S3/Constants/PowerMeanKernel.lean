/- GID: D5/S3/Constants/PowerMeanKernel
   generality: G
   mirror-B: D5/B/S3/Constants/PowerMeanKernel
   mirror-E: none(waiver:exact-algebraic-identities-only)
   anchors: []
   digest: Define the five rationalizable power means and their symmetric metric kernels. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace D5.S3.Constants.PowerMeanKernel

/-- The power mean at parameter `-1`. -/
noncomputable def meanNegOne (a b : ℝ) : ℝ := 2 * a * b / (a + b)

/-- The power mean at parameter `-1/2`. -/
noncomputable def meanNegHalf (a b : ℝ) : ℝ :=
  4 * a * b / (Real.sqrt a + Real.sqrt b) ^ 2

/-- The power mean at parameter `0`. -/
noncomputable def meanZero (a b : ℝ) : ℝ := Real.sqrt (a * b)

/-- The power mean at parameter `1/2`. -/
noncomputable def meanHalf (a b : ℝ) : ℝ :=
  (Real.sqrt a + Real.sqrt b) ^ 2 / 4

/-- The power mean at parameter `1`. -/
noncomputable def meanOne (a b : ℝ) : ℝ := (a + b) / 2

/-- The monotone-metric kernel induced by a symmetric mean. -/
noncomputable def symmetricKernel (mean : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  2 / mean (1 + t) (1 - t)

/-- The half-power mean is the pointwise average of the geometric and arithmetic means. -/
theorem meanHalf_eq_average (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    meanHalf a b = (meanZero a b + meanOne a b) / 2 := by
  rw [meanHalf, meanZero, meanOne]
  have hsqrt : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
    rw [Real.sqrt_mul ha]
  rw [hsqrt]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- The harmonic member on symmetric inputs is `1 - t^2`. -/
theorem meanNegOne_symmetric (t : ℝ) :
    meanNegOne (1 + t) (1 - t) = 1 - t ^ 2 := by
  rw [meanNegOne]
  ring

/-- The arithmetic member on symmetric inputs is one. -/
theorem meanOne_symmetric (t : ℝ) : meanOne (1 + t) (1 - t) = 1 := by
  rw [meanOne]
  ring

end D5.S3.Constants.PowerMeanKernel

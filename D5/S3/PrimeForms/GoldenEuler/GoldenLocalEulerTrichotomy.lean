/- GID: D5/S3/PrimeForms/GoldenEuler/GoldenLocalEulerTrichotomy
   generality: G
   mirror-B: D5/B/S3/PrimeForms/GoldenEuler/GoldenLocalEulerTrichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The neutral and quadratic charge denominator specializes to split, inert, and ramified golden local Euler forms. -/

import Mathlib

/-!
The variable `X` represents the local monomial `p^{-s}`. The theorem is purely
algebraic, so it remains valid independently of analytic convergence. The
charge values `1`, `-1`, and `0` encode split, inert, and ramified local types.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.PrimeForms.GoldenEuler.GoldenLocalEulerTrichotomy

/-- Product of the neutral denominator and one quadratic charge denominator. -/
def goldenLocalDenominator (charge X : ℝ) : ℝ :=
  (1 - X) * (1 - charge * X)

/-- Associated totalized local factor. -/
def goldenLocalFactor (charge X : ℝ) : ℝ :=
  (goldenLocalDenominator charge X)⁻¹

/-- Split charge gives two degree-one local factors. -/
theorem split_local_denominator (X : ℝ) :
    goldenLocalDenominator 1 X = (1 - X) ^ 2 := by
  unfold goldenLocalDenominator
  ring

/-- Inert charge fuses the pair into one degree-two factor. -/
theorem inert_local_denominator (X : ℝ) :
    goldenLocalDenominator (-1) X = 1 - X ^ 2 := by
  unfold goldenLocalDenominator
  ring

/-- Ramification removes the nontrivial quadratic charge factor. -/
theorem ramified_local_denominator (X : ℝ) :
    goldenLocalDenominator 0 X = 1 - X := by
  unfold goldenLocalDenominator
  ring

/-- Split local Euler factor. -/
theorem split_local_factor (X : ℝ) :
    goldenLocalFactor 1 X = ((1 - X) ^ 2)⁻¹ := by
  rw [goldenLocalFactor, split_local_denominator]

/-- Inert local Euler factor. -/
theorem inert_local_factor (X : ℝ) :
    goldenLocalFactor (-1) X = (1 - X ^ 2)⁻¹ := by
  rw [goldenLocalFactor, inert_local_denominator]

/-- Ramified local Euler factor. -/
theorem ramified_local_factor (X : ℝ) :
    goldenLocalFactor 0 X = (1 - X)⁻¹ := by
  rw [goldenLocalFactor, ramified_local_denominator]

#print axioms split_local_denominator
#print axioms inert_local_denominator
#print axioms ramified_local_denominator
#print axioms split_local_factor
#print axioms inert_local_factor
#print axioms ramified_local_factor

end D5.S3.PrimeForms.GoldenEuler.GoldenLocalEulerTrichotomy

/- GID: D5/S3/Fourier/CotangentHeckeIdentity
   generality: G
   mirror-B: D5/B/S3/Fourier/CotangentHeckeIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Partial closure of theorem 5.10: the cotangent double-angle identity. -/

import Mathlib

namespace D5.S3.Fourier.CotangentHeckeIdentity

/- The leading trigonometric clause is total over Lean's inverse convention.
   The remaining regularized-function and numerical clauses of theorem 5.10
   stay unresolved in the source ledger. -/
theorem cotangent_double_angle (theta : ℝ) :
    Real.cot theta + Real.cot (theta + Real.pi / 2) =
      2 * Real.cot (2 * theta) := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  rw [Real.sin_add, Real.cos_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
  rw [Real.sin_two_mul, Real.cos_two_mul']
  by_cases hs : Real.sin theta = 0
  · by_cases hc : Real.cos theta = 0
    · simp [hs, hc]
    · simp [hs]
  · by_cases hc : Real.cos theta = 0
    · simp [hc]
    · field_simp [hs, hc]
      ring

/- Checked inhabitance witness for the theorem's trigonometric domain. -/
example : Real.sin (Real.pi / 4) ≠ 0 := by
  rw [Real.sin_pi_div_four]
  positivity

example : Real.cos (Real.pi / 4) ≠ 0 := by
  rw [Real.cos_pi_div_four]
  positivity

end D5.S3.Fourier.CotangentHeckeIdentity

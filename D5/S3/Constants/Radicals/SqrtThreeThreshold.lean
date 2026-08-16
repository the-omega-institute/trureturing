/- GID: D5/S3/Constants/Radicals/SqrtThreeThreshold
   generality: G
   mirror-B: D5/B/S3/Constants/Radicals/SqrtThreeThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Twice root three lies strictly above three. -/

import Mathlib.Analysis.Real.Sqrt

namespace D5.S3.Constants.Radicals.SqrtThreeThreshold

/-- Twice the square root of three lies strictly above three. -/
theorem three_lt_two_mul_sqrt_three :
    (3 : ℝ) < 2 * Real.sqrt 3 := by
  have h : (3 / 2 : ℝ) < Real.sqrt 3 :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  linarith

end D5.S3.Constants.Radicals.SqrtThreeThreshold

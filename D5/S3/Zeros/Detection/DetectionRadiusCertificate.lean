/- GID: D5/S3/Zeros/Detection/DetectionRadiusCertificate
   generality: I
   mirror-B: D5/B/S3/Zeros/Detection/DetectionRadiusCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The beta 0.51 and gamma 10^12 detection radius is exactly 10^1200. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace D5.S3.Zeros.Detection.DetectionRadiusCertificate

/-- At beta = 51/100 and gamma = 10^12, the logarithmic detection scale is
exactly 1200 log 10, and exponentiating it gives the exact radius 10^1200. -/
theorem detection_radius_ten_to_the_1200_certificate :
    Real.log ((10 : Real) ^ 12) / ((51 : Real) / 100 - 1 / 2) =
        1200 * Real.log 10 ∧
      Real.exp
          (Real.log ((10 : Real) ^ 12) / ((51 : Real) / 100 - 1 / 2)) =
        (10 : Real) ^ 1200 := by
  have hscale :
      Real.log ((10 : Real) ^ 12) / ((51 : Real) / 100 - 1 / 2) =
        1200 * Real.log 10 := by
    rw [Real.log_pow]
    norm_num
    field_simp
    ring
  constructor
  · exact hscale
  · rw [hscale]
    have hlog :
        Real.log ((10 : Real) ^ 1200) = 1200 * Real.log 10 := by
      rw [Real.log_pow]
      norm_num
    rw [← hlog]
    exact Real.exp_log (by positivity)

-- The displayed denominator is the nonzero exact gap 1/100.
example : (51 : Real) / 100 - 1 / 2 = 1 / 100 ∧ (1 / 100 : Real) ≠ 0 := by
  norm_num

end D5.S3.Zeros.Detection.DetectionRadiusCertificate

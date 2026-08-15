/- GID: D5/S3/Zeros/Detection/LogTimeDoubling
   generality: G
   mirror-B: D5/B/S3/Zeros/Detection/LogTimeDoubling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A log-time shift by log 2 / delta doubles a positive exponential mode. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace D5.S3.Zeros.Detection.LogTimeDoubling

/-- For a positive displacement `delta`, advancing logarithmic time by
`log 2 / delta` exactly doubles the exponential mode with growth rate `delta`. -/
theorem log_time_shift_doubles_exponential_mode (delta u : ℝ) (hdelta : 0 < delta) :
    Real.exp (delta * (u + Real.log 2 / delta)) =
      2 * Real.exp (delta * u) := by
  have hcancel : delta * (Real.log 2 / delta) = Real.log 2 := by
    field_simp [ne_of_gt hdelta]
  rw [mul_add, hcancel, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  ring

-- At unit displacement the same shift specializes without any side calculation.
example (u : ℝ) :
    Real.exp (1 * (u + Real.log 2 / 1)) = 2 * Real.exp (1 * u) :=
  log_time_shift_doubles_exponential_mode 1 u (by norm_num)

end D5.S3.Zeros.Detection.LogTimeDoubling

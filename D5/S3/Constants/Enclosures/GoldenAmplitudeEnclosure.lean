/- GID: D5/S3/Constants/Enclosures/GoldenAmplitudeEnclosure
   generality: I
   mirror-B: D5/B/S3/Constants/Enclosures/GoldenAmplitudeEnclosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certify the seven-digit enclosure of the exact golden amplitude. -/

import D5.S3.Constants.Values

namespace D5.S3.Constants.Enclosures.GoldenAmplitudeEnclosure

open D5.S3.Constants.Values

/-- The exact golden amplitude lies within `3.3e-7` of the recorded decimal center. -/
theorem ah_seven_digit_enclosure :
    |ah - (0.3408474 : ℝ)| ≤ 0.00000033 := by
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hl_sq : (2.236065936 : ℝ) ^ 2 < 5 := by norm_num
  have hu_sq : 5 < (2.236069104 : ℝ) ^ 2 := by norm_num
  have hl : (2.236065936 : ℝ) < Real.sqrt 5 := by nlinarith
  have hu : Real.sqrt 5 < (2.236069104 : ℝ) := by nlinarith
  rw [abs_le]
  simp only [ah]
  constructor <;> nlinarith

end D5.S3.Constants.Enclosures.GoldenAmplitudeEnclosure

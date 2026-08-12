/- GID: D5/S3/Midline/GoldenSpectralMarker
   generality: I
   mirror-B: D5/B/S3/Midline/GoldenSpectralMarker
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The reciprocal first golden exponent is the golden spectral marker. -/

import D5.S3.Analytic.GoldenEulerBeta

namespace D5.S3.Midline.GoldenSpectralMarker

open D5.S3.Analytic.GoldenEulerBeta

/-- The reciprocal of the first golden exponent is the spectral marker
`1 / goldenRatio ^ 2`. -/
theorem golden_spectral_marker :
    1 / o5Beta 1 = 1 / Real.goldenRatio ^ 2 := by
  rw [o5_beta_power_law.1]

end D5.S3.Midline.GoldenSpectralMarker

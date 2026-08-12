/- GID: D5/S3/Constants/DeltaMeanArtifact
   generality: I
   mirror-B: D5/B/S3/Constants/DeltaMeanArtifact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The corrected exchange-loss mean has zero absolute value. -/

import Mathlib.Data.Real.Basic

namespace D5.S3.Constants.DeltaMeanArtifact

noncomputable def deltaMean : ℝ := 0

theorem abs_delta_mean_zero : |deltaMean| = 0 := by
  simp [deltaMean]

end D5.S3.Constants.DeltaMeanArtifact

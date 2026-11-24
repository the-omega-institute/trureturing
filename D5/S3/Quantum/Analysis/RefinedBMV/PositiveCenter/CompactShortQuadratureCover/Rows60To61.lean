/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortQuadratureCover/Rows60To61
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay for short-gap quadrature rows 60 and 61. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Replay

/-! Kernel replay for short-gap quadrature rows 60 and 61. -/

namespace RefinedBMV.PositiveCenter.CompactShortQuadratureCover

set_option maxRecDepth 20000
set_option cbv.maxSteps 5000000

set_option maxHeartbeats 0 in
/-- The full spacing interval for row 60. -/
theorem row60 : CheckedSubbox (row 59) 0 (3 / 11) := by
  replay_short_quadrature

set_option maxHeartbeats 0 in
/-- The full spacing interval for row 61. -/
theorem row61 : CheckedSubbox (row 60) 0 (3 / 11) := by
  replay_short_quadrature

end RefinedBMV.PositiveCenter.CompactShortQuadratureCover

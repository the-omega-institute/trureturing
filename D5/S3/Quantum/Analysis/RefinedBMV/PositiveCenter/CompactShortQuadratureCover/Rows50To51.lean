/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortQuadratureCover/Rows50To51
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay for short-gap quadrature rows 50 and 51. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Replay

/-! Kernel replay for short-gap quadrature rows 50 and 51. -/

namespace RefinedBMV.PositiveCenter.CompactShortQuadratureCover

set_option maxRecDepth 20000
set_option cbv.maxSteps 5000000

set_option maxHeartbeats 0 in
/-- The full spacing interval for row 50. -/
theorem row50 : CheckedSubbox (row 49) 0 (3 / 11) := by
  replay_short_quadrature

set_option maxHeartbeats 0 in
/-- The full spacing interval for row 51. -/
theorem row51 : CheckedSubbox (row 50) 0 (3 / 11) := by
  replay_short_quadrature

end RefinedBMV.PositiveCenter.CompactShortQuadratureCover

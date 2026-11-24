/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortQuadratureCover/Rows46To47
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay for short-gap quadrature rows 46 and 47. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Replay

/-! Kernel replay for short-gap quadrature rows 46 and 47. -/

namespace RefinedBMV.PositiveCenter.CompactShortQuadratureCover

set_option maxRecDepth 20000
set_option cbv.maxSteps 5000000

set_option maxHeartbeats 0 in
/-- The full spacing interval for row 46. -/
theorem row46 : CheckedSubbox (row 45) 0 (3 / 11) := by
  replay_short_quadrature

set_option maxHeartbeats 0 in
/-- The full spacing interval for row 47. -/
theorem row47 : CheckedSubbox (row 46) 0 (3 / 11) := by
  replay_short_quadrature

end RefinedBMV.PositiveCenter.CompactShortQuadratureCover

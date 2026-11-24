/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortQuadratureCover/Rows32To33
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay for short-gap quadrature rows 32 and 33. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Replay

/-! Kernel replay for short-gap quadrature rows 32 and 33. -/

namespace RefinedBMV.PositiveCenter.CompactShortQuadratureCover

set_option maxRecDepth 20000
set_option cbv.maxSteps 5000000

set_option maxHeartbeats 0 in
/-- The full spacing interval for row 32. -/
theorem row32 : CheckedSubbox (row 31) 0 (3 / 11) := by
  replay_short_quadrature

set_option maxHeartbeats 0 in
/-- The lower spacing half of row 33. -/
theorem row33_low : CheckedSubbox (row 32) 0 (3 / 22) := by
  replay_short_quadrature

set_option maxHeartbeats 0 in
/-- The upper spacing half of row 33. -/
theorem row33_high : CheckedSubbox (row 32) (3 / 22) (3 / 11) := by
  replay_short_quadrature

end RefinedBMV.PositiveCenter.CompactShortQuadratureCover

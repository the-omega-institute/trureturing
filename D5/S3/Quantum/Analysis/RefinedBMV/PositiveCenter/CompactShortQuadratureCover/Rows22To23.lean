/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortQuadratureCover/Rows22To23
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay for short-gap quadrature rows 22 and 23. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Replay

/-! Kernel replay for short-gap quadrature rows 22 and 23. -/

namespace RefinedBMV.PositiveCenter.CompactShortQuadratureCover

set_option maxRecDepth 20000
set_option cbv.maxSteps 5000000

set_option maxHeartbeats 0 in
/-- The lower spacing half of row 22. -/
theorem row22_low : CheckedSubbox (row 21) 0 (3 / 22) := by
  replay_short_quadrature

set_option maxHeartbeats 0 in
/-- The upper spacing half of row 22. -/
theorem row22_high : CheckedSubbox (row 21) (3 / 22) (3 / 11) := by
  replay_short_quadrature

set_option maxHeartbeats 0 in
/-- The lower spacing half of row 23. -/
theorem row23_low : CheckedSubbox (row 22) 0 (3 / 22) := by
  replay_short_quadrature

set_option maxHeartbeats 0 in
/-- The upper spacing half of row 23. -/
theorem row23_high : CheckedSubbox (row 22) (3 / 22) (3 / 11) := by
  replay_short_quadrature

end RefinedBMV.PositiveCenter.CompactShortQuadratureCover

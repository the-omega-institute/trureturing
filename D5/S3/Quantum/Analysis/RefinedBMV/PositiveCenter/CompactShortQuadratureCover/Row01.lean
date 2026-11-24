/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortQuadratureCover/Row01
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay for short-gap quadrature row 1. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Replay
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureHighSpacing

/-! Kernel replay for short-gap quadrature row 1. -/

namespace RefinedBMV.PositiveCenter.CompactShortQuadratureCover

open private box orders checks scoreLower from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureHighSpacing

/-- The upper spacing half of row 1, using the existing kernel certificate. -/
theorem row01_high : CheckedSubbox (row 0) (3 / 22) (3 / 11) := by
  have hbox : row 0 = box := by cbv
  have horders : orders = uniformOrders := by
    unfold orders uniformOrders
    congr 1
    funext i
    fin_cases i <;> rfl
  unfold CheckedSubbox
  rw [hbox, ← horders]
  exact ⟨checks, scoreLower⟩

set_option maxRecDepth 20000
set_option cbv.maxSteps 5000000

set_option maxHeartbeats 0 in
/-- The lower spacing half of row 1. -/
theorem row01_low : CheckedSubbox (row 0) 0 (3 / 22) := by
  replay_short_quadrature

end RefinedBMV.PositiveCenter.CompactShortQuadratureCover

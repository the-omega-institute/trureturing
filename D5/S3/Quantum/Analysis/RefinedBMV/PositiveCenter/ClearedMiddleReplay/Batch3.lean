/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ClearedMiddleReplay/Batch3
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay of cleared middle-gap leaves 14 through 21 by zero-based index. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ClearedMiddleReplay.Staged

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ClearedMiddleGrid

open scoped Staged

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem batch3_checked (i : Fin 8) :
    (leafAt (batchIndex 14 (by decide) i)).Checked := by
  fin_cases i <;> replay_staged_cleared_middle_leaf

end RefinedBMV.PositiveCenter.CompactTaylorModel.ClearedMiddleGrid

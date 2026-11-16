/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width7/Classes0
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width7/Classes0
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Width-seven exact-budget transfer. -/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width7.Data
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
/-! One source-class chunk for cost measurement. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width7.Classes0
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width7.Data
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
local instance (p : Row) : Decidable (Canonical p) := by unfold Canonical; infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem class_successors :
    successors ![0,1,2,3,2,0,1] 1 = sampledSuccessors := by
  decide +kernel

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width7.Classes0

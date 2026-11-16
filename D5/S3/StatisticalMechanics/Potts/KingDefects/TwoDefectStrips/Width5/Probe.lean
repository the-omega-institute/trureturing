/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Probe
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Probe
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Width-five exact-budget transfer measurement. -/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Probe
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem transition_counts : ∀ p (d : Fin 3), Valid p d.val →
 (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
 cl r (d.val-(bondDefects between p r+bondDefects horizontal r r)) = (0 : Fin 43) then (1 : ℤ) else 0) = T (cl p d.val) 0 := by
 decide +kernel
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Probe

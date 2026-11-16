/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Classes0
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Classes0
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Width-six exact-budget transfer. -/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
/-! One source-class chunk for cost measurement. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes0
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
local instance (p : Row) : Decidable (Canonical p) := by unfold Canonical; infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem class_successors : ∀ p (d : Fin 3), Valid p d.val → Canonical p →
    cl p d.val = sampledClass → successors p d.val = sampledSuccessors := by
  have h : ∀ i : Fin (4^6), ∀ d : Fin 3, Valid (finFunctionFinEquiv.symm i) d.val → Canonical (finFunctionFinEquiv.symm i) → cl (finFunctionFinEquiv.symm i) d.val = sampledClass → successors (finFunctionFinEquiv.symm i) d.val = sampledSuccessors := by
    decide +kernel
  intro p
  simpa only [Equiv.symm_apply_apply] using h (finFunctionFinEquiv p)
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes0

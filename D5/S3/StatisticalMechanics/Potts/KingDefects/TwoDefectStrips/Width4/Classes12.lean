/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes12
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes12
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Width-4 exact-budget transfer measurement. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live path of HardinA229751.result)
class_successors: proof_shape=bind-only; consumers=Certificate.canonical_successors
-/

import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Data
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes12
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Data
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
local instance (p : Row) : Decidable (Canonical p) := by
  unfold Canonical
  infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem class_successors : ∀ p (d : Fin 3), Valid p d.val →
    Canonical p → cl p d.val = (12 : Fin 19) → successors p d.val = classList 12 := by
  decide +kernel
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes12

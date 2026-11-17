/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes0
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes0
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229751.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Certificate.transition_counts,D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Forward.structural_certificate
   digest: Width-4 exact-budget transfer measurement. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed helpers on the live path of HardinA229751.result)
class_successors: proof_shape=content; consumers=Certificate.canonical_successors
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Data
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes0
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Data
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip (Boundary)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
private local instance (p : Boundary) : Decidable (Canonical p) := by
  unfold Canonical
  infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem class_successors : ∀ p (d : Fin 3), Valid p d.val →
    Canonical p → cl p d.val = (0 : Fin 19) → successors p d.val = classList 0 := by
  decide +kernel
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes0

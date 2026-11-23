/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Classes8
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Classes8
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Certificate.transition_counts; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Classes8.class_successors
   digest: Width-3 exact-budget transfer measurement. -/

/-
admission_basis: escape-witness
escape_witness: class_successors verifies the sorted successor multiplicities of every valid canonical width-3 source in class 8. Certificate.canonical_successors substitutes that list into the width-3 transfer sum.
class_successors: proof_shape=content; consumers=Certificate.canonical_successors
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233163KingStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Data
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Classes8
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Data
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233163KingStrip (Boundary)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
private local instance (p : Boundary) : Decidable (Canonical p) := by
  unfold Canonical
  infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem class_successors : ∀ p (d : Fin 3), Valid p d.val →
    Canonical p → cl p d.val = (8 : Fin 9) → successors p d.val = classList 8 := by
  decide +kernel
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Classes8

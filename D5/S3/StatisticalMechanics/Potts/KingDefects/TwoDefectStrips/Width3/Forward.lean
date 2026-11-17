/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Forward
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Forward
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229750.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Certificate.transition_counts,D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Forward.structural_certificate
   digest: Width-3 exact-budget transfer measurement. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed helpers on the live path of HardinA229750.result)
structural_certificate: proof_shape=content; consumers=HardinA229750.result
-/

import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Data
/-! Acceptance, initial weights and the forward polynomial relation. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Forward
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Data
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233163KingStrip (Boundary)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem structural_certificate :
    (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ s : Fin 9, (∑ r : Boundary, if bondDefects horizontal r r ≤ 2 ∧
      cl r (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 8, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 8 = ∑ j : Fin 6, (![-8, 36, -66, 63, -33, 9] j : ℤ) • W ⟨2+j.val, by omega⟩ := by
  decide +kernel
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Forward

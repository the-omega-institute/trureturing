/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Pins/Initial17
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Pins/Initial17
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Coordinate certificates for the width-six transfer. -/
/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live path of HardinA229753.result)
certificate: proof_shape=bind-only; consumers=Width6.Forward.structural_certificate
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
/-! Finite coordinate identities for exact-budget transfer. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial17
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate : ∀ s : Fin 4,
    (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl r (2 - bondDefects horizontal r r) = (⟨68+s.val, by omega⟩ : Fin 96) then (1 : ℤ) else 0) = initial (⟨68+s.val, by omega⟩ : Fin 96) := by
  decide +kernel

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial17

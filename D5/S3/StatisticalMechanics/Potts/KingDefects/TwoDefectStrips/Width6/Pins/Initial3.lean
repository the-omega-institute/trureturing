/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Pins/Initial3
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Pins/Initial3
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229753.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Certificate.transition_counts,D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Forward.structural_certificate
   digest: Coordinate certificates for the width-six transfer. -/
/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed helpers on the live path of HardinA229753.result)
own_certificate: proof_shape=content; consumers=certificate
certificate: proof_shape=content; consumers=Width6.Pins.Initial4.certificate
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial2
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
/-! Finite coordinate identities for exact-budget transfer. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial3
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem own_certificate : ∀ s : Fin 12,
    (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl r (2 - bondDefects horizontal r r) = (⟨36+s.val, by omega⟩ : Fin 96) then (1 : ℤ) else 0) = initial (⟨36+s.val, by omega⟩ : Fin 96) := by
  decide +kernel

theorem certificate : ∀ s : Fin 36,
    (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl r (2 - bondDefects horizontal r r) = (⟨12+s.val, by omega⟩ : Fin 96) then (1 : ℤ) else 0) = initial (⟨12+s.val, by omega⟩ : Fin 96) := by
  intro s
  by_cases hs : s.val < 24
  · exact Pins.Initial2.certificate ⟨s.val, hs⟩
  · have h := own_certificate ⟨s.val - 24, by omega⟩
    have he : 36 + (s.val - 24) = 12 + s.val := by omega
    simpa only [he] using h

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial3

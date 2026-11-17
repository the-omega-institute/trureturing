/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Krylov/Check7
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Krylov/Check7
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Coordinate certificates for the width-six transfer. -/
/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live path of HardinA229753.result)
own_certificate: proof_shape=bind-only; consumers=certificate
certificate: proof_shape=bind-only; consumers=Width6.Forward.structural_certificate
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check6
/-! Finite coordinate identities for exact-budget transfer. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check7
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem own_certificate :
    (∀ (i : Fin 11) (s : Fin 12), W i.succ (⟨84+s.val, by omega⟩ : Fin 96) =
      Matrix.vecMul (W i.castSucc) T (⟨84+s.val, by omega⟩ : Fin 96)) ∧
    (∀ s : Fin 12, W 11 (⟨84+s.val, by omega⟩ : Fin 96) =
      (∑ j : Fin 6, (![-8,36,-66,63,-33,9] j : ℤ) • W ⟨5+j.val, by omega⟩) (⟨84+s.val, by omega⟩ : Fin 96)) := by
  decide +kernel

theorem certificate :
    (∀ (i : Fin 11) (s : Fin 96), W i.succ (⟨0+s.val, by omega⟩ : Fin 96) =
      Matrix.vecMul (W i.castSucc) T (⟨0+s.val, by omega⟩ : Fin 96)) ∧
    (∀ s : Fin 96, W 11 (⟨0+s.val, by omega⟩ : Fin 96) =
      (∑ j : Fin 6, (![-8,36,-66,63,-33,9] j : ℤ) • W ⟨5+j.val, by omega⟩) (⟨0+s.val, by omega⟩ : Fin 96)) := by
  constructor
  · intro i s
    by_cases hs : s.val < 84
    · exact Krylov.Check6.certificate.1 i ⟨s.val, hs⟩
    · have h := own_certificate.1 i ⟨s.val - 84, by omega⟩
      have he : 84 + (s.val - 84) = 0 + s.val := by omega
      simpa only [he] using h
  · intro s
    by_cases hs : s.val < 84
    · exact Krylov.Check6.certificate.2 ⟨s.val, hs⟩
    · have h := own_certificate.2 ⟨s.val - 84, by omega⟩
      have he : 84 + (s.val - 84) = 0 + s.val := by omega
      simpa only [he] using h

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check7

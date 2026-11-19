/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Krylov/Check6
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Krylov/Check6
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Coordinate certificates for the width-six transfer. -/
/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: own_certificate (computed matrix updates and recurrence equality at coordinates 72 through 83 used by certificate)
own_certificate: proof_shape=content; consumers=certificate
certificate: proof_shape=content; consumers=Width6.Krylov.Check7.certificate
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check5
/-! Finite coordinate identities for exact-budget transfer. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check6
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem own_certificate :
    (∀ (i : Fin 11) (s : Fin 12), W i.succ (⟨72+s.val, by omega⟩ : Fin 96) =
      Matrix.vecMul (W i.castSucc) T (⟨72+s.val, by omega⟩ : Fin 96)) ∧
    (∀ s : Fin 12, W 11 (⟨72+s.val, by omega⟩ : Fin 96) =
      (∑ j : Fin 6, (![-8,36,-66,63,-33,9] j : ℤ) • W ⟨5+j.val, by omega⟩) (⟨72+s.val, by omega⟩ : Fin 96)) := by
  decide +kernel

theorem certificate :
    (∀ (i : Fin 11) (s : Fin 84), W i.succ (⟨0+s.val, by omega⟩ : Fin 96) =
      Matrix.vecMul (W i.castSucc) T (⟨0+s.val, by omega⟩ : Fin 96)) ∧
    (∀ s : Fin 84, W 11 (⟨0+s.val, by omega⟩ : Fin 96) =
      (∑ j : Fin 6, (![-8,36,-66,63,-33,9] j : ℤ) • W ⟨5+j.val, by omega⟩) (⟨0+s.val, by omega⟩ : Fin 96)) := by
  constructor
  · intro i s
    by_cases hs : s.val < 72
    · exact Krylov.Check5.certificate.1 i ⟨s.val, hs⟩
    · have h := own_certificate.1 i ⟨s.val - 72, by omega⟩
      have he : 72 + (s.val - 72) = 0 + s.val := by omega
      simpa only [he] using h
  · intro s
    by_cases hs : s.val < 72
    · exact Krylov.Check5.certificate.2 ⟨s.val, hs⟩
    · have h := own_certificate.2 ⟨s.val - 72, by omega⟩
      have he : 72 + (s.val - 72) = 0 + s.val := by omega
      simpa only [he] using h

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check6

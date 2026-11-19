/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Krylov/Check1
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Krylov/Check1
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229753.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Krylov/Check1.certificate
   digest: Coordinate certificates for the width-six transfer. -/
/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live path of HardinA229753.result)
own_certificate: proof_shape=bind-only; consumers=certificate
certificate: proof_shape=bind-only; consumers=Width6.Krylov.Check2.certificate
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check0
/-! Finite coordinate identities for exact-budget transfer. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check1
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem own_certificate :
    (∀ (i : Fin 11) (s : Fin 12), W i.succ (⟨12+s.val, by omega⟩ : Fin 96) =
      Matrix.vecMul (W i.castSucc) T (⟨12+s.val, by omega⟩ : Fin 96)) ∧
    (∀ s : Fin 12, W 11 (⟨12+s.val, by omega⟩ : Fin 96) =
      (∑ j : Fin 6, (![-8,36,-66,63,-33,9] j : ℤ) • W ⟨5+j.val, by omega⟩) (⟨12+s.val, by omega⟩ : Fin 96)) := by
  decide +kernel

theorem certificate :
    (∀ (i : Fin 11) (s : Fin 24), W i.succ (⟨0+s.val, by omega⟩ : Fin 96) =
      Matrix.vecMul (W i.castSucc) T (⟨0+s.val, by omega⟩ : Fin 96)) ∧
    (∀ s : Fin 24, W 11 (⟨0+s.val, by omega⟩ : Fin 96) =
      (∑ j : Fin 6, (![-8,36,-66,63,-33,9] j : ℤ) • W ⟨5+j.val, by omega⟩) (⟨0+s.val, by omega⟩ : Fin 96)) := by
  constructor
  · intro i s
    by_cases hs : s.val < 12
    · exact Krylov.Check0.certificate.1 i ⟨s.val, hs⟩
    · have h := own_certificate.1 i ⟨s.val - 12, by omega⟩
      have he : 12 + (s.val - 12) = 0 + s.val := by omega
      simpa only [he] using h
  · intro s
    by_cases hs : s.val < 12
    · exact Krylov.Check0.certificate.2 ⟨s.val, hs⟩
    · have h := own_certificate.2 ⟨s.val - 12, by omega⟩
      have he : 12 + (s.val - 12) = 0 + s.val := by omega
      simpa only [he] using h

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check1

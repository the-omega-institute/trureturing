/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Counts/Check3
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Counts/Check3
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229753.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Counts/Check3.counts
   digest: Exact multiplicities of width-six class successors. -/
/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live path of HardinA229753.result)
own_counts: proof_shape=bind-only; consumers=counts
counts: proof_shape=bind-only; consumers=Width6.Counts.Check4.counts
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check2
/-! Exact successor multiplicities for the first 48 classes. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check3
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
set_option maxRecDepth 100000 in
private theorem own_counts : ∀ c : Fin 12, ∀ s : Fin 96,
    ((classList (⟨36+c.val, by omega⟩ : Fin 96)).count s : ℤ) =
      T (⟨36+c.val, by omega⟩ : Fin 96) s := by
  intro c
  fin_cases c <;> decide +kernel
set_option maxRecDepth 100000 in
theorem counts : ∀ c : Fin 48, ∀ s : Fin 96,
    ((classList (⟨c.val, by omega⟩ : Fin 96)).count s : ℤ) =
      T (⟨c.val, by omega⟩ : Fin 96) s := by
  intro c s
  by_cases hi : c.val < 36
  · exact Check2.counts ⟨c.val, hi⟩ s
  · have h := own_counts ⟨c.val - 36, by omega⟩ s
    have he : 36 + (c.val - 36) = c.val := by omega
    simpa only [he] using h
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check3

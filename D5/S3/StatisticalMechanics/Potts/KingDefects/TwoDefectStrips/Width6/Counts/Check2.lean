/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Counts/Check2
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Counts/Check2
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229753.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Counts/Check2.counts
   digest: Exact multiplicities of width-six class successors. -/
/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (literal classList multiplicities and T coefficients normalize; no new row-successor proposition)
own_counts: proof_shape=bind-only; consumers=counts; reason=Literal classList/T entries for classes 24 through 35 reduce to finite list/count arithmetic.
counts: proof_shape=bind-only; consumers=Width6.Counts.Check3.counts; reason=After inlining own_counts, combines the preceding range with literal normalization for classes 24 through 35.
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check1
/-! Exact successor multiplicities for the first 36 classes. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check2
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
set_option maxRecDepth 100000 in
private theorem own_counts : ∀ c : Fin 12, ∀ s : Fin 96,
    ((classList (⟨24+c.val, by omega⟩ : Fin 96)).count s : ℤ) =
      T (⟨24+c.val, by omega⟩ : Fin 96) s := by
  intro c
  fin_cases c <;> decide +kernel
set_option maxRecDepth 100000 in
theorem counts : ∀ c : Fin 36, ∀ s : Fin 96,
    ((classList (⟨c.val, by omega⟩ : Fin 96)).count s : ℤ) =
      T (⟨c.val, by omega⟩ : Fin 96) s := by
  intro c s
  by_cases hi : c.val < 24
  · exact Check1.counts ⟨c.val, hi⟩ s
  · have h := own_counts ⟨c.val - 24, by omega⟩ s
    have he : 24 + (c.val - 24) = c.val := by omega
    simpa only [he] using h
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check2

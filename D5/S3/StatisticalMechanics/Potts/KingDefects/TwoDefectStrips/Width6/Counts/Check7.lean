/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Counts/Check7
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Counts/Check7
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229753.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Counts/Check7.counts
   digest: Exact multiplicities of width-six class successors. -/
/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: own_counts (computed successor multiplicities for source classes 84 through 95 used by counts)
own_counts: proof_shape=content; consumers=counts
counts: proof_shape=content; consumers=Width6.Certificate.transition_counts
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check6
/-! Exact successor multiplicities for the first 96 classes. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check7
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
set_option maxRecDepth 100000 in
private theorem own_counts : ∀ c : Fin 12, ∀ s : Fin 96,
    ((classList (⟨84+c.val, by omega⟩ : Fin 96)).count s : ℤ) =
      T (⟨84+c.val, by omega⟩ : Fin 96) s := by
  intro c
  fin_cases c <;> decide +kernel
set_option maxRecDepth 100000 in
theorem counts : ∀ c : Fin 96, ∀ s : Fin 96,
    ((classList (⟨c.val, by omega⟩ : Fin 96)).count s : ℤ) =
      T (⟨c.val, by omega⟩ : Fin 96) s := by
  intro c s
  by_cases hi : c.val < 84
  · exact Check6.counts ⟨c.val, hi⟩ s
  · have h := own_counts ⟨c.val - 84, by omega⟩ s
    have he : 84 + (c.val - 84) = c.val := by omega
    simpa only [he] using h
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check7

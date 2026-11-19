/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Counts/Check0
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Counts/Check0
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact multiplicities of width-six class successors. -/
/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live path of HardinA229753.result)
counts: proof_shape=bind-only; consumers=Width6.Counts.Check1.counts
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
/-! Exact successor multiplicities for the first 12 classes. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check0
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
set_option maxRecDepth 100000 in
theorem counts : ∀ c : Fin 12, ∀ s : Fin 96,
    ((classList (⟨c.val, by omega⟩ : Fin 96)).count s : ℤ) =
      T (⟨c.val, by omega⟩ : Fin 96) s := by
  intro c
  fin_cases c <;> decide +kernel
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check0

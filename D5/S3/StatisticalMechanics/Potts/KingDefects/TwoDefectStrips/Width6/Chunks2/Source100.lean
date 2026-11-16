/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Chunks2/Source100
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Chunks2/Source100
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Width-six source states 300 through 302. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live path of HardinA229753.result)
successor_rows: proof_shape=bind-only; consumers=Width6.Certificate.source_successors
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Sources
/-! Successor multisets at explicit canonical source states. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks2.Source100
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Sources
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem successor_rows : ∀ i : Fin 3,
    successors (sources ⟨300+i.val, by omega⟩).1 (sources ⟨300+i.val, by omega⟩).2.val =
      classList (cl (sources ⟨300+i.val, by omega⟩).1
        (sources ⟨300+i.val, by omega⟩).2.val) := by
  decide +kernel
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks2.Source100

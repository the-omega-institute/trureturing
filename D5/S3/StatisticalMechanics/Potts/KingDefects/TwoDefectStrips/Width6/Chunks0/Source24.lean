/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Chunks0/Source24
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Chunks0/Source24
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229753.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Certificate.transition_counts,D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Forward.structural_certificate
   digest: Width-six source states 138 through 146. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed helpers on the live path of HardinA229753.result)
own_rows: proof_shape=content; consumers=successor_rows
successor_rows: proof_shape=content; consumers=Width6.Chunks0.Source25.successor_rows
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Sources
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source23
/-! Successor multisets at explicit canonical source states. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source24
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Sources
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem own_rows : ∀ i : Fin 9,
    successors (sources ⟨138+i.val, by omega⟩).1 (sources ⟨138+i.val, by omega⟩).2.val =
      classList (cl (sources ⟨138+i.val, by omega⟩).1
        (sources ⟨138+i.val, by omega⟩).2.val) := by
  intro i
  fin_cases i <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem successor_rows : ∀ i : Fin 147,
    successors (sources ⟨0+i.val, by omega⟩).1 (sources ⟨0+i.val, by omega⟩).2.val =
      classList (cl (sources ⟨0+i.val, by omega⟩).1
        (sources ⟨0+i.val, by omega⟩).2.val) := by
  intro i
  by_cases hi : i.val < 138
  · exact Chunks0.Source23.successor_rows ⟨i.val, hi⟩
  · have h := own_rows ⟨i.val - 138, by omega⟩
    have he : 138 + (i.val - 138) = 0 + i.val := by omega
    simpa only [he] using h

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source24

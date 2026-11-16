/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Classes29
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Classes29
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Width-six exact successor classes 87 through 89. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helper on the live path of HardinA229753.result)
class_successors: proof_shape=bind-only; consumers=Width6.Certificate.canonical_successors
-/

import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
/-! Three source classes of the canonical-boundary defect transfer. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes29
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Rows
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem class_successors (c : Fin 3) : ∀ p (d : Fin 3), Valid p d.val →
    Canonical p → cl p d.val = (⟨87+c.val, by omega⟩ : Fin 96) →
    successors p d.val = classList ⟨87+c.val, by omega⟩ := by
  have h : ∀ (i : Fin 187) (d : Fin 3) (c : Fin 3), Valid (rows i) d.val →
      cl (rows i) d.val = (⟨87+c.val, by omega⟩ : Fin 96) →
      successors (rows i) d.val = classList ⟨87+c.val, by omega⟩ := by
    decide +kernel
  intro p d hp hc he
  have hr := reconstruction p hc
  rw [← hr] at hp he ⊢
  exact h (rowIndex p) d c hp he
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes29

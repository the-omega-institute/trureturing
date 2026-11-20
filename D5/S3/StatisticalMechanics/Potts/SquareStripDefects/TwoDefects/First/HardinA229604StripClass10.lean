/- GID: D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass10
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/First/HardinA229604StripClass10
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604Strip.result; premises=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604Strip.finite_certificate
   digest: Exact residual-budget square-lattice strip transfer. -/

/-
admission_basis: open-problem-resolution (#31660; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229604Strip.result)
transition_counts: proof_shape=bind-only; consumers=HardinA229604StripClasses.transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut

/-! New two-defect target columns. -/
open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229584StripData (Row horizontal)
namespace D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.First.HardinA229604StripClass10
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open HardinA229604StripData
open HardinA233177Canonical (Canonical)
theorem transition_counts (j : Fin 2) : ∀ p (d : Fin 3), Valid p d.val → Canonical p →
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = (⟨62 + j.val, by omega⟩ : Fin 96)
      then (1 : ℤ) else 0) = T (cl p d.val) (⟨62 + j.val, by omega⟩ : Fin 96) := by
  have remaining : ∀ p (d : Fin 3), Valid p d.val → Canonical p →
      d.val + bondDefects horizontal p p = 2 → (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = (⟨62 + j.val, by omega⟩ : Fin 96)
      then (1 : ℤ) else 0) = T (cl p d.val) (⟨62 + j.val, by omega⟩ : Fin 96) := by
    unfold Canonical
    rw [Fin.forall_fin_succ_pi]
    intro c0
    rw [Fin.forall_fin_succ_pi]
    intro c1
    rw [Fin.forall_fin_succ_pi]
    intro c2
    rw [Fin.forall_fin_succ_pi]
    intro c3
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3 <;> decide +kernel +revert
  intro p d hp hc
  by_cases hz : d.val = 0 ∧ bondDefects horizontal p p ≤ 1
  · have he : (⟨62 + j.val, by omega⟩ : Fin 96) = ((⟨20 + j.val, by omega⟩ : Fin 32).natAdd 42).castAdd 22 := by
      apply Fin.ext
      dsimp
      omega
    rw [hz.1, he]
    exact HardinA229604StripCut.terminal_counts p hz.2 ⟨20 + j.val, by omega⟩
  · by_cases ho : d.val = 1 ∧ bondDefects horizontal p p = 0
    · have he : (⟨62 + j.val, by omega⟩ : Fin 96) = ((⟨20 + j.val, by omega⟩ : Fin 32).natAdd 42).castAdd 22 := by
        apply Fin.ext
        dsimp
        omega
      rw [ho.1, he]
      exact HardinA229604StripCut.one_defect_counts p ho.2 ⟨20 + j.val, by omega⟩
    · exact remaining p d hp hc (by dsimp only [Valid] at hp; omega)

end D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.First.HardinA229604StripClass10

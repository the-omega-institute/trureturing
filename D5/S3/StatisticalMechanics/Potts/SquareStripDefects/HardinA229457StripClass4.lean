/- GID: D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripClass4
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripClass4
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip.result; premises=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip.finite_certificate
   digest: Exact residual-budget square-lattice strip transfer. -/

/-
admission_basis: open-problem-resolution (#31660; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229457Strip.result)
transition_counts: proof_shape=bind-only; consumers=HardinA229457StripClasses.transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

/-! Exact residual-budget square-lattice strip transfer. -/

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229584StripData (Row horizontal)
namespace D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClass4
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open HardinA229457StripData
open HardinA233177Canonical (Canonical)
theorem transition_counts (j : Fin 4) : ∀ p (d : Fin 2), Valid p d.val → Canonical p →
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = (⟨26 + j.val, by omega⟩ : Fin 42)
      then (1 : ℤ) else 0) = T (cl p d.val) ⟨26 + j.val, by omega⟩ := by
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

end D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClass4

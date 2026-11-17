/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripClass13
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripClass13
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.finite_certificate
   digest: Exact width-six one-defect HDA transfer. -/

/-
admission_basis: open-problem-resolution (#31328; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229532Strip.result)
transition_counts: proof_shape=bind-only; consumers=HardinA229532StripClasses.transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripCut
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233172DiagonalStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

/-! Exact width-six HDA residual-budget transfer. -/
open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
open D5.S3.Combinatorics.TraceAvoidingArrays
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass13
open DefectTransfer (bondDefects)
open HardinA229584StripData (Row horizontal)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option synthInstance.maxSize 100000
open HardinA229532StripData
open HardinA233177Canonical (Canonical)
theorem transition_counts : ∀ p (d : Fin 2), Valid p d.val → Canonical p →
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 13
      then (1 : ℤ) else 0) = T (cl p d.val) 13 := by
  have table : ∀ p (d : Fin 2), HardinThinGraphTransport.proper p ∧ d.val = 0 →
      HardinA233172DiagonalStrip.transfer
        (HardinA233172DiagonalStrip.boundaryClass (true, true) p) 4 / 64 =
          T (cl p d.val) 13 := by decide +kernel
  have remaining : ∀ p (d : Fin 2), Valid p d.val → Canonical p →
      ¬ (HardinThinGraphTransport.proper p ∧ d.val = 0) →
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 13
        then (1 : ℤ) else 0) = T (cl p d.val) 13 := by
    unfold Canonical
    intro p d
    fin_cases d <;> revert p <;> decide +kernel
  intro p d hp hn
  by_cases hz : HardinThinGraphTransport.proper p ∧ d.val = 0
  · simp_rw [HardinA229532StripCut.class_cut p _ d 13 (by right; exact ⟨hz.2, by decide⟩)]
    have h := raw_successors p hz.1 4
    exact (Int.eq_ediv_of_mul_eq_right (by decide) h).trans (table p d hz)
  · exact remaining p d hp hn hz
end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass13

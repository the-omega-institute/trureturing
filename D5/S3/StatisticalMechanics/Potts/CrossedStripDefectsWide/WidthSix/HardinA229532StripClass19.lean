/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripClass19
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripClass19
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.finite_certificate
   digest: Exact width-six one-defect HDA transfer. -/

/-
admission_basis: open-problem-resolution (#31328; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229532Strip.result)
proper_table: proof_shape=bind-only; consumers=transition_counts
remaining_counts: proof_shape=bind-only; consumers=transition_counts
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
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass19
open DefectTransfer (bondDefects)
open HardinA229584StripData (Row horizontal)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option synthInstance.maxSize 100000
open HardinA229532StripData
open HardinA233177Canonical (Canonical)
private theorem proper_table : ∀ p (d : Fin 2), HardinThinGraphTransport.proper p ∧ d.val = 0 →
    HardinA233172DiagonalStrip.transfer
      (HardinA233172DiagonalStrip.boundaryClass (true, true) p) 10 / 64 =
        T (cl p d.val) 19 := by decide +kernel

private theorem remaining_counts : ∀ p (d : Fin 2), Valid p d.val → Canonical p →
    ¬ (HardinThinGraphTransport.proper p ∧ d.val = 0) →
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 19
      then (1 : ℤ) else 0) = T (cl p d.val) 19 := by
  unfold Canonical
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +kernel +revert

theorem transition_counts : ∀ p (d : Fin 2), Valid p d.val → Canonical p →
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 19
      then (1 : ℤ) else 0) = T (cl p d.val) 19 := by
  intro p d hp hn
  by_cases hz : HardinThinGraphTransport.proper p ∧ d.val = 0
  · have cut (r : Row) :
        ((bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
          cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 19) ↔
          HardinThinGraphTransport.proper r ∧
            HardinThinGraphTransport.compatible true p r ∧
            HardinA233172DiagonalStrip.boundaryClass (true, true) r = 10) := by
      exact HardinA229532StripCut.class_cut p r d 19 (by
        right; exact ⟨hz.2, by decide⟩)
    simp_rw [cut]
    have h := raw_successors p hz.1 10
    exact (Int.eq_ediv_of_mul_eq_right (by decide) h).trans (proper_table p d hz)
  · exact remaining_counts p d hp hn hz
end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass19

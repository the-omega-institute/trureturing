/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripClass11
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripClass11
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.finite_certificate
   digest: Exact width-six one-defect HDA transfer. -/

/-
admission_basis: open-problem-resolution (#31328; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229532Strip.result)
proper_entries: proof_shape=bind-only; consumers=proper_table
proper_table: proof_shape=bind-only; consumers=transition_counts
remaining_zero: proof_shape=bind-only; consumers=transition_counts
remaining_one: proof_shape=bind-only; consumers=transition_counts
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
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass11
open DefectTransfer (bondDefects)
open HardinA229584StripData (Row horizontal)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option synthInstance.maxSize 100000
open HardinA229532StripData
open HardinA233177Canonical (Canonical)

private theorem proper_entries : ∀ i : Fin 11, i ≠ 0 →
    HardinA233172DiagonalStrip.transfer i 2 / 64 =
      T ⟨i.val - 1 + 10, by omega⟩ 11 := by decide +kernel

private theorem proper_table : ∀ p (d : Fin 2), HardinThinGraphTransport.proper p ∧ d.val = 0 →
    HardinA233172DiagonalStrip.transfer
      (HardinA233172DiagonalStrip.boundaryClass (true, true) p) 2 / 64 =
        T (cl p d.val) 11 := by
  intro p d hp
  have hproper : bondDefects horizontal p p = 0 := by
    simp only [bondDefects, Finset.card_filter_eq_zero_iff, horizontal,
      HardinA229584StripData.horizontal, Finset.forall_mem_image, Finset.mem_univ,
      forall_const]
    exact hp.1
  simp only [cl, hproper, ↓reduceIte, hp.2, Nat.lt_irrefl]
  have hi : HardinA233172DiagonalStrip.boundaryClass (true, true) p ≠ 0 := by
    simp only [HardinA233172DiagonalStrip.boundaryClass, Bool.true_eq, ↓reduceIte]
    split_ifs <;> decide
  exact proper_entries _ hi

private theorem remaining_zero : ∀ p, Canonical p → Valid p 0 →
    ¬ (HardinThinGraphTransport.proper p ∧ 0 = 0) →
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ 0 ∧
      cl r (0 - (bondDefects between p r + bondDefects horizontal r r)) = 11
      then (1 : ℤ) else 0) = T (cl p 0) 11 := by
  unfold Canonical
  rw [Fin.forall_fin_succ_pi]
  intro c0
  rw [Fin.forall_fin_succ_pi]
  intro c1
  rw [Fin.forall_fin_succ_pi]
  intro c2
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> decide +kernel

private theorem remaining_one : ∀ p, Canonical p → Valid p 1 →
    ¬ (HardinThinGraphTransport.proper p ∧ 1 = 0) →
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ 1 ∧
      cl r (1 - (bondDefects between p r + bondDefects horizontal r r)) = 11
      then (1 : ℤ) else 0) = T (cl p 1) 11 := by
  unfold Canonical
  rw [Fin.forall_fin_succ_pi]
  intro c0
  rw [Fin.forall_fin_succ_pi]
  intro c1
  rw [Fin.forall_fin_succ_pi]
  intro c2
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> decide +kernel

theorem transition_counts : ∀ p (d : Fin 2), Valid p d.val → Canonical p →
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 11
      then (1 : ℤ) else 0) = T (cl p d.val) 11 := by
  intro p d hp hn
  by_cases hz : HardinThinGraphTransport.proper p ∧ d.val = 0
  · have cut (r : Row) :
        ((bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
          cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 11) ↔
          HardinThinGraphTransport.proper r ∧
            HardinThinGraphTransport.compatible true p r ∧
            HardinA233172DiagonalStrip.boundaryClass (true, true) r = 2) := by
      exact HardinA229532StripCut.class_cut p r d 11 (by
        right; exact ⟨hz.2, by decide⟩)
    simp_rw [cut]
    have h := raw_successors p hz.1 2
    exact (Int.eq_ediv_of_mul_eq_right (by decide) h).trans (proper_table p d hz)
  · fin_cases d
    · exact remaining_zero p hn hp hz
    · exact remaining_one p hn hp hz
end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass11

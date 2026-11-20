/- GID: D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripCut
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripCut
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip.result; premises=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip.finite_certificate
   digest: Exact residual-budget square-lattice strip transfer. -/

/-
admission_basis: open-problem-resolution (#31660; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229457Strip.result)
zero_cost: proof_shape=bind-only; consumers=class_cut
numeric_cut: proof_shape=bind-only; consumers=class_cut
class_cut: proof_shape=bind-only; consumers=active_counts, HardinA229457StripClass0.transition_counts through HardinA229457StripClass2.transition_counts
proper_table: proof_shape=bind-only; consumers=proper_counts
proper_counts: proof_shape=bind-only; consumers=active_counts, HardinA229457StripClass0.transition_counts through HardinA229457StripClass2.transition_counts
active_counts: proof_shape=bind-only; consumers=HardinA229457StripClasses.transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport

/-! Exact residual-budget square-lattice strip transfer. -/

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229584StripData (Row horizontal)
namespace D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open HardinA229457StripData
private theorem zero_cost (p r : Row) :
    bondDefects ProperTransfer.between p r + bondDefects horizontal r r = 0 ↔
      HardinThinGraphTransport.proper r ∧ (∀ i : Fin 6, p i ≠ r i) := by
  simp only [Nat.add_eq_zero_iff, bondDefects, Finset.card_filter_eq_zero_iff,
    ProperTransfer.between, Finset.diag, Finset.map_eq_image,
    HardinA229584StripData.horizontal, Finset.forall_mem_image,
    Finset.mem_univ, forall_const, HardinThinGraphTransport.proper]
  tauto

private theorem numeric_cut : ∀ (r : Row) (c d : Fin 2) (s : Fin 20),
    ((d.val = 1 ∧ s.val < 10) ∨ (d.val = 0 ∧ 10 ≤ s.val)) →
    ((c.val ≤ d.val ∧ cl r (d.val - c.val) = s.castAdd 22) ↔
      c.val = 0 ∧ HardinThinGraphTransport.proper r ∧
        HardinA233127SquareStrip.boundaryClass (true, true) r =
          ⟨s.val % 10 + 1, by have := Nat.mod_lt s.val (by omega : 0 < 10); omega⟩) := by
  intro r
  generalize h0 : r 0 = c0
  generalize h1 : r 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +kernel +revert

theorem class_cut (p r : Row) (d : Fin 2) (s : Fin 20)
    (hs : (d.val = 1 ∧ s.val < 10) ∨ (d.val = 0 ∧ 10 ≤ s.val)) :
    ((bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = s.castAdd 22) ↔
      HardinThinGraphTransport.proper r ∧ (∀ i : Fin 6, p i ≠ r i) ∧
        HardinA233127SquareStrip.boundaryClass (true, true) r =
          ⟨s.val % 10 + 1, by have := Nat.mod_lt s.val (by omega : 0 < 10); omega⟩) := by
  by_cases hc : bondDefects ProperTransfer.between p r + bondDefects horizontal r r < 2
  · rw [numeric_cut r ⟨_, hc⟩ d s hs, zero_cost]
    tauto
  · have hn : ¬ (bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val) := by omega
    have hz := zero_cost p r
    have hp : ¬ (HardinThinGraphTransport.proper r ∧ (∀ i : Fin 6, p i ≠ r i)) := by
      intro h
      have := hz.mpr h
      omega
    simp only [hn, false_and]
    tauto

private theorem proper_table : ∀ p (d : Fin 2) (s : Fin 20), HardinThinGraphTransport.proper p →
      ((d.val = 1 ∧ s.val < 10) ∨ (d.val = 0 ∧ 10 ≤ s.val)) →
      HardinA233127SquareStrip.transfer
        (HardinA233127SquareStrip.boundaryClass (true, true) p)
        ⟨s.val % 10 + 1, by have := Nat.mod_lt s.val (by omega : 0 < 10); omega⟩ / 64 =
      T (cl p d.val) (s.castAdd 22) := by decide +kernel

theorem proper_counts (p : Row) (d : Fin 2) (hp : HardinThinGraphTransport.proper p)
    (s : Fin 20) (hs : (d.val = 1 ∧ s.val < 10) ∨ (d.val = 0 ∧ 10 ≤ s.val)) :
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = s.castAdd 22
      then (1 : ℤ) else 0) = T (cl p d.val) (s.castAdd 22) := by
  simp_rw [class_cut p _ d s hs]
  have h := ProperTransfer.raw_successors p hp
    ⟨s.val % 10 + 1, by have := Nat.mod_lt s.val (by omega : 0 < 10); omega⟩
  exact (Int.eq_ediv_of_mul_eq_right (by decide) h).trans (proper_table p d s hp hs)

theorem active_counts (j : Fin 10) : ∀ p (d : Fin 2), Valid p d.val →
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = j.castAdd 32
      then (1 : ℤ) else 0) = T (cl p d.val) (j.castAdd 32) := by
  intro p d hp
  have hz : d.val = 0 ∨ d.val = 1 := by omega
  rcases hz with hd | hd
  · have hn : ∀ r (c : ℕ), ¬ (c ≤ 0 ∧ cl r (0-c) = j.castAdd 32) := by
      have h : ∀ r : Row, 10 ≤ (cl r 0).val := by decide +kernel
      intro r c hc
      have hh := congrArg Fin.val hc.2
      have hl := h r
      simp only [Nat.zero_sub, Fin.val_castAdd] at hh
      omega
    simp_rw [hd, ite_eq_right (hn _ _)]
    have table : ∀ p (j : Fin 10), T (cl p 0) (j.castAdd 32) = 0 := by decide +kernel
    simpa using (table p j).symm
  · have hp0 : HardinThinGraphTransport.proper p := by
      have proper : bondDefects horizontal p p = 0 ↔ HardinThinGraphTransport.proper p := by
        simp only [bondDefects, HardinA229584StripData.horizontal, Finset.card_filter_eq_zero_iff,
          Finset.forall_mem_image, Finset.mem_univ, forall_const,
          HardinThinGraphTransport.proper]
      apply proper.mp
      dsimp only [Valid,
      D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData.Valid] at hp
      omega
    have h := proper_counts p d hp0 (j.castAdd 10) (Or.inl ⟨hd, j.isLt⟩)
    exact h

end D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut

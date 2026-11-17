/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripCut
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripCut
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.finite_certificate
   digest: Exact width-six one-defect HDA transfer. -/

/-
admission_basis: open-problem-resolution (#31328; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229532Strip.result)
zero_cost: proof_shape=bind-only; consumers=class_cut
numeric_cut: proof_shape=bind-only; consumers=class_cut
class_cut: proof_shape=bind-only; consumers=HardinA229532StripTop.transition_counts and HardinA229532StripClass10.transition_counts through HardinA229532StripClass19.transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233172DiagonalStrip

/-! Exact width-six HDA residual-budget transfer. -/
open D5.S3.StatisticalMechanics.Potts.StripDefects
open D5.S3.Combinatorics.TraceAvoidingArrays
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripCut
open DefectTransfer (bondDefects)
open HardinA229584StripData (Row horizontal)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option synthInstance.maxSize 100000
open HardinA229532StripData
private theorem zero_cost (p r : Row) :
    bondDefects between p r + bondDefects horizontal r r = 0 ↔
      HardinThinGraphTransport.proper r ∧ HardinThinGraphTransport.compatible true p r := by
  simp only [Nat.add_eq_zero_iff, bondDefects, Finset.card_filter_eq_zero_iff]
  simp only [between, horizontal, HardinA229584StripData.horizontal,
    HardinA229584StripData.antidiagonal, Finset.forall_mem_union, Finset.forall_mem_image,
    Finset.mem_univ, forall_const, Prod.fst, Prod.snd, Prod.swap_prod_mk]
  simp only [HardinThinGraphTransport.proper, HardinThinGraphTransport.compatible,
    Bool.true_eq, ↓reduceIte, forall_and]
  tauto

private theorem numeric_cut : ∀ (r : Row) (c d : Fin 2) (s : Fin 20),
    ((d.val = 1 ∧ s.val < 10) ∨ (d.val = 0 ∧ 10 ≤ s.val)) →
    ((c.val ≤ d.val ∧ cl r (d.val - c.val) = s.castAdd 11) ↔
      c.val = 0 ∧ HardinThinGraphTransport.proper r ∧
        HardinA233172DiagonalStrip.boundaryClass (true, true) r =
          ⟨s.val % 10 + 1, by have := Nat.mod_lt s.val (by omega : 0 < 10); omega⟩) := by
  intro r
  generalize h0 : r 0 = c0
  generalize h1 : r 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +kernel +revert

/-- Zero-cost transitions select the corresponding published proper boundary class. -/
theorem class_cut (p r : Row) (d : Fin 2) (s : Fin 20)
    (hs : (d.val = 1 ∧ s.val < 10) ∨ (d.val = 0 ∧ 10 ≤ s.val)) :
    ((bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s.castAdd 11) ↔
      HardinThinGraphTransport.proper r ∧ HardinThinGraphTransport.compatible true p r ∧
        HardinA233172DiagonalStrip.boundaryClass (true, true) r =
          ⟨s.val % 10 + 1, by have := Nat.mod_lt s.val (by omega : 0 < 10); omega⟩) := by
  by_cases hc : bondDefects between p r + bondDefects horizontal r r < 2
  · rw [numeric_cut r ⟨_, hc⟩ d s hs]
    rw [zero_cost p r]
    tauto
  · have hn : ¬ (bondDefects between p r + bondDefects horizontal r r ≤ d.val) := by omega
    have hz := zero_cost p r
    have hp : ¬ (HardinThinGraphTransport.proper r ∧
        HardinThinGraphTransport.compatible true p r) := by
      intro h
      have := hz.mpr h
      omega
    simp only [hn, false_and]
    tauto

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripCut

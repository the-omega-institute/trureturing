/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripCut
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripCut
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531Strip.finite_certificate
   digest: Exact HDA defect transfer and Hardin's registered recurrence. -/

/-
admission_basis: open-problem-resolution (#31121; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229531Strip.result)
zero_cost: proof_shape=bind-only; consumers=class_cut
numeric_cut: proof_shape=bind-only; consumers=class_cut
class_cut: proof_shape=bind-only; consumers=HardinA229531StripClass0.transition_counts through HardinA229531StripClass11.transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripData

/-! Structural zero-defect cuts for the inherited proper-colouring blocks. -/
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripCut
open HardinA229531StripData
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem zero_cost (p r : Row) :
    bondDefects between p r + bondDefects horizontal r r = 0 ↔
      HardinThinGraphTransport.proper r ∧ HardinThinGraphTransport.compatible true p r := by
  simp only [Nat.add_eq_zero_iff, bondDefects, Finset.card_filter_eq_zero_iff]
  simp only [between, horizontal, HardinA229583StripData.horizontal,
    HardinA229583StripData.antidiagonal, Finset.forall_mem_union, Finset.forall_mem_image,
    Finset.mem_univ, forall_const, Prod.fst, Prod.snd, Prod.swap_prod_mk]
  simp only [HardinThinGraphTransport.proper, HardinThinGraphTransport.compatible,
    Bool.true_eq, ↓reduceIte, forall_and]
  tauto

private theorem numeric_cut : ∀ (r : Row) (c d : Fin 2) (s : Fin 12),
    ((d.val = 1 ∧ s.val < 6) ∨ (d.val = 0 ∧ 6 ≤ s.val)) →
    ((c.val ≤ d.val ∧ cl r (d.val - c.val) = s.castAdd 8) ↔
      c.val = 0 ∧ HardinThinGraphTransport.proper r ∧
        HardinA233126SquareStrip.boundaryClass (true, true) r =
          ⟨s.val % 6 + 1, by have := Nat.mod_lt s.val (by omega : 0 < 6); omega⟩) := by
  intro r
  generalize h0 : r 0 = c0
  generalize h1 : r 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +kernel +revert

/-- Zero-cost transitions select the corresponding published proper boundary class. -/
theorem class_cut (p r : Row) (d : Fin 2) (s : Fin 12)
    (hs : (d.val = 1 ∧ s.val < 6) ∨ (d.val = 0 ∧ 6 ≤ s.val)) :
    ((bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s.castAdd 8) ↔
      HardinThinGraphTransport.proper r ∧ HardinThinGraphTransport.compatible true p r ∧
        HardinA233126SquareStrip.boundaryClass (true, true) r =
          ⟨s.val % 6 + 1, by have := Nat.mod_lt s.val (by omega : 0 < 6); omega⟩) := by
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

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripCut

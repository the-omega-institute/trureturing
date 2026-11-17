/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripTop
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripTop
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

/-! Exact width-six HDA residual-budget transfer. -/
open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
open D5.S3.Combinatorics.TraceAvoidingArrays
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripTop
open DefectTransfer (bondDefects)
open HardinA229584StripData (Row horizontal antidiagonal)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option synthInstance.maxSize 100000
open HardinA229532StripData
theorem transition_counts (j : Fin 10) : ∀ p (d : Fin 2), Valid p d.val →
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = j.castAdd 21
      then (1 : ℤ) else 0) = T (cl p d.val) (j.castAdd 21) := by
  intro p d hp
  have proper (r : Row) : bondDefects horizontal r r = 0 ↔ HardinThinGraphTransport.proper r := by
    simp only [bondDefects, Finset.card_filter_eq_zero_iff, HardinA229584StripData.horizontal,
      Finset.forall_mem_image, Finset.mem_univ, forall_const, Prod.fst, Prod.snd,
      HardinThinGraphTransport.proper]
  have hz : d.val = 0 ∨ d.val = 1 := by omega
  rcases hz with hd | hd
  · have hn : ∀ r (c : ℕ), ¬ (c ≤ 0 ∧ cl r (0-c) = j.castAdd 21) := by
      have h : ∀ (r : Row), (cl r 0).val ≥ 10 := by decide +kernel
      intro r c hc
      have hh := congrArg Fin.val hc.2
      have hl := h r
      simp only [Nat.zero_sub, Fin.val_castAdd] at hh
      omega
    simp_rw [hd, if_neg (hn _ _)]
    have table : ∀ p (j : Fin 10), T (cl p 0) (j.castAdd 21) = 0 := by decide +kernel
    simpa using (table p j).symm
  · have hp0 : HardinThinGraphTransport.proper p := by
      apply (proper p).mp
      dsimp only [Valid] at hp
      omega
    have hc (r : Row) := HardinA229532StripCut.class_cut p r d (j.castAdd 10) (by
      left; exact ⟨hd, by simp only [Fin.val_castAdd]; omega⟩)
    have he : (j.castAdd 10).castAdd 11 = j.castAdd 21 := by apply Fin.ext; rfl
    have hm : (j.val % 10 + 1) = j.val + 1 := by rw [Nat.mod_eq_of_lt j.isLt]
    simp only [he, Fin.val_castAdd, hm] at hc
    simp_rw [hc]
    have h := raw_successors p hp0 ⟨j.val + 1, by omega⟩
    have table : ∀ p (d : Fin 2) (j : Fin 10), HardinThinGraphTransport.proper p →
        d.val = 1 → HardinA233172DiagonalStrip.transfer
          (HardinA233172DiagonalStrip.boundaryClass (true, true) p) ⟨j.val+1, by omega⟩ / 64 =
            T (cl p d.val) (j.castAdd 21) := by decide +kernel
    exact (Int.eq_ediv_of_mul_eq_right (by decide) h).trans (table p d j hp0 hd)
end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripTop

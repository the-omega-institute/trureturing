/- GID: D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripCut
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripCut
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604Strip.result; premises=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604Strip.finite_certificate
   digest: Exact residual-budget square-lattice strip transfer. -/

/-
admission_basis: open-problem-resolution (#31660; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229604Strip.result)
zero_lower: proof_shape=bind-only; consumers=active_cut, leading_counts
active_cut: proof_shape=bind-only; consumers=leading_counts
leading_counts: proof_shape=bind-only; consumers=HardinA229604StripClasses.transition_counts
terminal_cut: proof_shape=bind-only; consumers=terminal_counts
terminal_counts: proof_shape=bind-only; consumers=TwoDefects.First.HardinA229604StripClass0.transition_counts, TwoDefects.First.HardinA229604StripClass1.transition_counts, TwoDefects.First.HardinA229604StripClass2.transition_counts, TwoDefects.First.HardinA229604StripClass3.transition_counts, TwoDefects.First.HardinA229604StripClass4.transition_counts, TwoDefects.First.HardinA229604StripClass5.transition_counts, TwoDefects.First.HardinA229604StripClass6.transition_counts, TwoDefects.First.HardinA229604StripClass7.transition_counts, TwoDefects.First.HardinA229604StripClass8.transition_counts, TwoDefects.First.HardinA229604StripClass9.transition_counts, TwoDefects.First.HardinA229604StripClass10.transition_counts, TwoDefects.First.HardinA229604StripClass11.transition_counts, TwoDefects.First.HardinA229604StripClass12.transition_counts, TwoDefects.First.HardinA229604StripClass13.transition_counts, TwoDefects.Last.HardinA229604StripClass14.transition_counts, TwoDefects.Last.HardinA229604StripClass15.transition_counts
one_defect_cut: proof_shape=bind-only; consumers=one_defect_counts
one_defect_counts: proof_shape=bind-only; consumers=TwoDefects.First.HardinA229604StripClass0.transition_counts, TwoDefects.First.HardinA229604StripClass1.transition_counts, TwoDefects.First.HardinA229604StripClass2.transition_counts, TwoDefects.First.HardinA229604StripClass3.transition_counts, TwoDefects.First.HardinA229604StripClass4.transition_counts, TwoDefects.First.HardinA229604StripClass5.transition_counts, TwoDefects.First.HardinA229604StripClass6.transition_counts, TwoDefects.First.HardinA229604StripClass7.transition_counts, TwoDefects.First.HardinA229604StripClass8.transition_counts, TwoDefects.First.HardinA229604StripClass9.transition_counts, TwoDefects.First.HardinA229604StripClass10.transition_counts, TwoDefects.First.HardinA229604StripClass11.transition_counts, TwoDefects.First.HardinA229604StripClass12.transition_counts, TwoDefects.First.HardinA229604StripClass13.transition_counts, TwoDefects.Last.HardinA229604StripClass14.transition_counts, TwoDefects.Last.HardinA229604StripClass15.transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClasses

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229584StripData (Row horizontal)
namespace D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open HardinA229604StripData
private theorem zero_lower (p : Row) : 42 ≤ (cl p 0).val := by
  have h : ∀ p : Row, 42 ≤ (cl p 0).val := by decide +kernel
  exact h p

theorem active_cut (r : Row) (c : ℕ) (d : Fin 3) (j : Fin 42) (hd : 0 < d.val) :
    ((c ≤ d.val ∧ cl r (d.val - c) = j.castAdd 54) ↔
      c ≤ d.val - 1 ∧ HardinA229457StripData.cl r (d.val - 1 - c) = j) := by
  by_cases hc : c < d.val
  · have hn : 0 < d.val - c := by omega
    have he : d.val - c - 1 = d.val - 1 - c := by omega
    have hcl : cl r (d.val - c) =
        (HardinA229457StripData.cl r (d.val - 1 - c)).castAdd 54 := by
      rw [cl, if_pos hn, he]
    simp only [hcl, Fin.ext_iff, Fin.val_castAdd]
    omega
  · have hz := zero_lower r
    have hn : d.val - c = 0 := by omega
    have hh : cl r (d.val - c) ≠ j.castAdd 54 := by
      intro he
      have := congrArg Fin.val he
      rw [hn] at this
      change (cl r 0).val = j.val at this
      omega
    have hc0 : ¬ c ≤ d.val - 1 := by omega
    simp only [hh, hc0, and_false, false_and]

theorem leading_counts (p : Row) (d : Fin 3) (hp : Valid p d.val) (j : Fin 42) :
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = j.castAdd 54
      then (1 : ℤ) else 0) = T (cl p d.val) (j.castAdd 54) := by
  by_cases hd : 0 < d.val
  · have hv : HardinA229457StripData.Valid p (d.val - 1) := by
      dsimp only [Valid, HardinA229457StripData.Valid,
        D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData.Valid] at hp ⊢
      omega
    simp_rw [active_cut _ _ d j hd]
    have h := HardinA229457StripClasses.transition_counts p
      ⟨d.val - 1, by have := hp.1; omega⟩ hv j
    have ht : T (cl p d.val) (j.castAdd 54) =
        HardinA229457StripData.T (HardinA229457StripData.cl p (d.val - 1)) j := by
      rw [cl, if_pos hd]
      exact leading_block _ j
    exact h.trans ht.symm
  · have hz : d.val = 0 := by omega
    have hn : ∀ r (c : ℕ), ¬ (c ≤ 0 ∧ cl r (0 - c) = j.castAdd 54) := by
      intro r c hc
      have h := zero_lower r
      have he := congrArg Fin.val hc.2
      simp only [Nat.zero_sub, Fin.val_castAdd] at he
      omega
    simp_rw [hz, if_neg (hn _ _)]
    have ht : T (cl p 0) (j.castAdd 54) = 0 := by
      have hl := zero_lower p
      simp only [T, Fin.val_castAdd, j.isLt, ↓reduceDIte]
      simp only [show ¬ (cl p 0).val < 42 by omega, ↓reduceDIte]
    simpa using ht.symm

private theorem terminal_cut (p r : Row) (j : Fin 32) :
    ((bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ 0 ∧
      cl r (0 - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = (j.natAdd 42).castAdd 22) ↔
      bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ 0 ∧
        HardinA229457StripData.cl r (0 - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = j.natAdd 10) := by
  by_cases hc : bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ 0
  · have hr : bondDefects horizontal r r ≤ 1 := by omega
    simp only [hc, true_and, Nat.zero_sub, cl, Nat.lt_irrefl, ↓reduceIte, hr,
      Fin.ext_iff, Fin.val_mk, Fin.val_castAdd, Fin.val_natAdd]
    omega
  · simp only [hc, false_and]

theorem terminal_counts (p : Row) (hp : bondDefects horizontal p p ≤ 1) (j : Fin 32) :
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ 0 ∧
      cl r (0 - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = (j.natAdd 42).castAdd 22
      then (1 : ℤ) else 0) = T (cl p 0) ((j.natAdd 42).castAdd 22) := by
  simp_rw [terminal_cut p _ j]
  have hv : HardinA229457StripData.Valid p 0 := by
    exact ⟨by omega, by simpa only [Nat.sub_zero] using hp⟩
  have h := HardinA229457StripClasses.transition_counts p 0 hv (j.natAdd 10)
  have ht : T (cl p 0) ((j.natAdd 42).castAdd 22) =
      HardinA229457StripData.T (HardinA229457StripData.cl p 0) (j.natAdd 10) := by
    have hl : 10 ≤ (HardinA229457StripData.cl p 0).val := by
      have h : ∀ p : Row, 10 ≤ (HardinA229457StripData.cl p 0).val := by decide +kernel
      exact h p
    let i : Fin 32 := ⟨(HardinA229457StripData.cl p 0).val - 10, by
      have := (HardinA229457StripData.cl p 0).isLt
      omega⟩
    have hc : cl p 0 = (i.natAdd 42).castAdd 22 := by
      simp only [cl, Nat.lt_irrefl, ↓reduceIte, hp]
      apply Fin.ext
      dsimp [i]
      omega
    have ho : HardinA229457StripData.cl p 0 = i.natAdd 10 := by
      apply Fin.ext
      dsimp [i]
      omega
    rw [hc, terminal_block, ← ho]
  exact h.trans ht.symm

private theorem one_defect_cut (p r : Row) (j : Fin 32) :
    ((DefectTransfer.bondDefects ProperTransfer.between p r +
      DefectTransfer.bondDefects horizontal r r ≤ 1 ∧
      HardinA229604StripData.cl r (1 - (DefectTransfer.bondDefects ProperTransfer.between p r +
        DefectTransfer.bondDefects horizontal r r)) = (j.natAdd 42).castAdd 22) ↔
    DefectTransfer.bondDefects ProperTransfer.between p r +
      DefectTransfer.bondDefects horizontal r r ≤ 1 ∧
      HardinA229457StripData.cl r (1 - (DefectTransfer.bondDefects ProperTransfer.between p r +
        DefectTransfer.bondDefects horizontal r r)) = j.natAdd 10) := by
  let c := DefectTransfer.bondDefects ProperTransfer.between p r +
    DefectTransfer.bondDefects horizontal r r
  change (c ≤ 1 ∧ HardinA229604StripData.cl r (1-c) = (j.natAdd 42).castAdd 22) ↔
    c ≤ 1 ∧ HardinA229457StripData.cl r (1-c) = j.natAdd 10
  by_cases hc : c ≤ 1
  · have hr : DefectTransfer.bondDefects horizontal r r ≤ 1 := by dsimp [c] at hc; omega
    rcases (show c = 0 ∨ c = 1 by omega) with h0 | h1
    · have hr0 : DefectTransfer.bondDefects horizontal r r = 0 := by dsimp [c] at h0; omega
      have hn : (HardinA229604StripData.cl r 1).val < 42 := by
        simpa only [HardinA229604StripData.cl, show 0 < (1 : ℕ) by decide,
          ite_eq_left, Nat.sub_self, Fin.val_castAdd] using (HardinA229457StripData.cl r 0).isLt
      have ho : (HardinA229457StripData.cl r 1).val < 10 := by
        simpa only [HardinA229457StripData.cl, hr0, ite_eq_left, show 0 < (1 : ℕ) by decide,
          Fin.val_castAdd] using (ProperTransfer.cl r).isLt
      simp only [h0, Nat.sub_zero, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
      omega
    · simp only [h1, Nat.sub_self, HardinA229604StripData.cl,
        Nat.lt_irrefl, ite_false, hr, ite_true, Fin.ext_iff,
        Fin.val_castAdd, Fin.val_natAdd]
      omega
  · simp only [hc, false_and]
theorem one_defect_counts (p : Row) (hp : DefectTransfer.bondDefects horizontal p p = 0) (j : Fin 32) :
    (∑ r : Row, if DefectTransfer.bondDefects ProperTransfer.between p r +
      DefectTransfer.bondDefects horizontal r r ≤ 1 ∧
      HardinA229604StripData.cl r (1 - (DefectTransfer.bondDefects ProperTransfer.between p r +
        DefectTransfer.bondDefects horizontal r r)) = (j.natAdd 42).castAdd 22
      then (1 : ℤ) else 0) =
      HardinA229604StripData.T (HardinA229604StripData.cl p 1) ((j.natAdd 42).castAdd 22) := by
  simp_rw [one_defect_cut p _ j]
  have h := HardinA229457StripClasses.transition_counts p 1
    (show HardinA229457StripData.Valid p 1 from ⟨by decide, by simp [hp]⟩) (j.natAdd 10)
  have ht : HardinA229604StripData.T (((ProperTransfer.cl p).natAdd 10).castAdd 76)
        ((j.natAdd 42).castAdd 22) =
      HardinA229457StripData.T ((ProperTransfer.cl p).castAdd 32) (j.natAdd 10) := by
    have hi : (((ProperTransfer.cl p).natAdd 10).castAdd 76).val < 42 := by dsimp; omega
    have hi₀ : ¬ (((ProperTransfer.cl p).natAdd 10).castAdd 76).val < 10 := by dsimp; omega
    have hi₁ : (((ProperTransfer.cl p).natAdd 10).castAdd 76).val < 20 := by dsimp; omega
    have hj : ¬ ((j.natAdd 42).castAdd 22).val < 42 := by dsimp; omega
    have hj₁ : ((j.natAdd 42).castAdd 22).val < 74 := by dsimp; omega
    simp only [T, hi, hi₀, hi₁, hj, hj₁, ↓reduceDIte]
    congr 1 <;> apply Fin.ext <;> dsimp <;> omega
  have hc1 : HardinA229457StripData.cl p 1 = (ProperTransfer.cl p).castAdd 32 := by
    simp only [HardinA229457StripData.cl, hp, ite_eq_left, show 0 < (1 : ℕ) by decide]
  have hc0 : (HardinA229457StripData.cl p 0).castAdd 54 =
      ((ProperTransfer.cl p).natAdd 10).castAdd 76 := by
    apply Fin.ext
    simp only [HardinA229457StripData.cl, hp, ite_eq_left, Nat.lt_irrefl, ite_false,
      Fin.val_castAdd, Fin.val_natAdd]
  simp only [Fin.val_one] at h
  rw [hc1] at h
  simpa only [HardinA229604StripData.cl, show 0 < (1 : ℕ) by decide,
    ite_eq_left, Nat.sub_self, hc0] using h.trans ht.symm

end D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut

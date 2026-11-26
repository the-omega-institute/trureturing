/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripCut
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripCut
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip.finite_certificate
   digest: The two-defect extension of the five-row HA quotient. -/

/-
admission_basis: open-problem-resolution (#31594; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229698Strip.result)
old_cut: proof_shape=bind-only; consumers=tuple_counts
new_cut: proof_shape=bind-only; consumers=tuple_counts
spent_one_cut: proof_shape=bind-only; consumers=tuple_counts
spent_two_cut: proof_shape=bind-only; consumers=tuple_counts
tuple_counts: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=bind-only; consumers=HardinA229698Strip.count_transfer
initial_counts: proof_shape=bind-only; consumers=HardinA229698Strip.count_transfer
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripCut
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripNew
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripNew

/-! Exact three-colour counts on five-row HA strips with two defects. -/

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripCut
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
open D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590
open HardinA229698StripData

set_option maxRecDepth 100000
set_option Elab.async false

set_option maxHeartbeats 0 in
private theorem old_cut (p : Col) (d : Fin 2) (r : Col)
    (s : Fin 41 ⊕ Fin 41) :
    (HardinA229590StripData.cross p (column r) ≤ d.val ∧
      cl r (d.val - HardinA229590StripData.cross p (column r)) = Sum.inr s) ↔
    (HardinA229590StripData.cross p (column r) ≤ d.val ∧
      HardinA229590StripData.cl r (d.val - HardinA229590StripData.cross p (column r)) = s) := by
  have h : d.val - HardinA229590StripData.cross p (column r) ≠ 2 := by omega
  simp only [cl, h, ↓reduceIte, Sum.inr.injEq]

set_option maxHeartbeats 0 in
private theorem new_cut (c : ℕ) (r : Col) (s : Fin 41) :
    (c ≤ 2 ∧ cl r (2-c) = Sum.inl s) ↔ c = 0 ∧ cls r = s := by
  by_cases h : c = 0
  · simp [h, cl]
  · have h2 : 2-c ≠ 2 := by omega
    simp [cl, h2, h]

set_option maxHeartbeats 0 in
private theorem spent_one_cut (c : ℕ) (r : Col) (s : Fin 41) :
    (c ≤ 2 ∧ cl r (2-c) = Sum.inr (Sum.inl s)) ↔ c = 1 ∧ cls r = s := by
  by_cases h0 : c = 0
  · simp [h0, cl]
  · by_cases h1 : c = 1
    · simp [h1, cl, HardinA229590StripData.cl]
    · by_cases h2 : c = 2
      · simp [h2, cl, HardinA229590StripData.cl]
      · have hc : ¬ c ≤ 2 := by omega
        simp [hc, h1]

set_option maxHeartbeats 0 in
private theorem spent_two_cut (c : ℕ) (r : Col) (s : Fin 41) :
    (c ≤ 2 ∧ cl r (2-c) = Sum.inr (Sum.inr s)) ↔ c = 2 ∧ cls r = s := by
  by_cases h0 : c = 0
  · simp [h0, cl]
  · by_cases h1 : c = 1
    · simp [h1, cl, HardinA229590StripData.cl]
    · by_cases h2 : c = 2
      · simp [h2, cl, HardinA229590StripData.cl]
      · have hc : ¬ c ≤ 2 := by omega
        simp [hc, h2]

set_option maxHeartbeats 0 in
private theorem tuple_counts (p : Col) (d : Fin 3) (s : Fin 41 ⊕ (Fin 41 ⊕ Fin 41)) :
    (∑ c : Col, if HardinA229590StripData.cross p (column c) ≤ d.val ∧
      cl c (d.val - HardinA229590StripData.cross p (column c)) = s then (1 : ℤ) else 0) =
      T (cl p d.val) s := by
  by_cases hd : d.val = 2
  · have de : d = 2 := Fin.ext hd
    subst d
    cases s with
    | inl j =>
      simp_rw [show (2 : Fin 3).val = 2 from rfl, new_cut]
      have h := HardinA229590StripCut.transition_counts p 0 (Sum.inr j)
      rw [← HardinA229590StripCut.column_sum (fun c =>
        if HardinA229590StripData.cross p (column c) = 0 ∧ cls c = j then (1 : ℤ) else 0)]
      simpa only [HardinA229590StripCut.column_boundary, Fin.val_zero,
        Nat.le_zero, Nat.zero_sub, HardinA229590StripData.cl, ↓reduceIte,
        Sum.inr.injEq, HardinA229590StripData.T, Matrix.fromBlocks,
        T, cl, Sum.elim_inl, Sum.elim_inr, Matrix.of_apply] using h
    | inr s =>
      cases s with
      | inl j =>
        simp_rw [show (2 : Fin 3).val = 2 from rfl, spent_one_cut]
        exact HardinA229590StripNew.quotient_rows p j
      | inr j =>
        simp_rw [show (2 : Fin 3).val = 2 from rfl, spent_two_cut]
        exact HardinA229698StripNew.quotient_rows p j
  · have hlt : d.val < 2 := by omega
    cases s with
    | inl j =>
      have he (c : Col) : ¬ (HardinA229590StripData.cross p (column c) ≤ d.val ∧
          cl c (d.val - HardinA229590StripData.cross p (column c)) = Sum.inl j) := by
        have hne : d.val - HardinA229590StripData.cross p (column c) ≠ 2 := by omega
        simp only [cl, hne, ↓reduceIte, Sum.inr_ne_inl, and_false, not_false_eq_true]
      have zsum : (∑ c : Col, if HardinA229590StripData.cross p (column c) ≤ d.val ∧
          cl c (d.val - HardinA229590StripData.cross p (column c)) = Sum.inl j
          then (1 : ℤ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro c hc
        exact if_neg (he c)
      rw [zsum]
      simp [cl, hd, T, Matrix.fromBlocks]
    | inr s =>
      simp_rw [old_cut p ⟨d.val,hlt⟩]
      have h := HardinA229590StripCut.transition_counts p ⟨d.val,hlt⟩ s
      rw [← HardinA229590StripCut.column_sum (fun c =>
        if HardinA229590StripData.cross p (column c) ≤ d.val ∧
          HardinA229590StripData.cl c (d.val - HardinA229590StripData.cross p (column c)) = s
          then (1 : ℤ) else 0)]
      simpa only [HardinA229590StripCut.column_boundary, cl, hd, ↓reduceIte,
        T, Matrix.fromBlocks, Sum.elim_inl, Sum.elim_inr, Matrix.of_apply] using h

set_option maxHeartbeats 0 in
theorem transition_counts (p : Col) (d : Fin 3) (s : Fin 41 ⊕ (Fin 41 ⊕ Fin 41)) :
    (∑ r : Fin 5 → Fin 3, if HardinA229590StripData.cross p r ≤ d.val ∧
      cl (HardinA229590StripData.boundary r) (d.val - HardinA229590StripData.cross p r) = s
      then (1 : ℤ) else 0) = T (cl p d.val) s := by
  calc
    _ = ∑ r : Fin 5 → Fin 3, if HardinA229590StripData.cross p
        (column (HardinA229590StripData.boundary r)) ≤ d.val ∧
      cl (HardinA229590StripData.boundary r) (d.val - HardinA229590StripData.cross p
        (column (HardinA229590StripData.boundary r))) = s then (1 : ℤ) else 0 := by
      simp_rw [HardinA229590StripCut.column_boundary]
    _ = _ := (HardinA229590StripCut.column_sum (fun c =>
      if HardinA229590StripData.cross p (column c) ≤ d.val ∧
        cl c (d.val - HardinA229590StripData.cross p (column c)) = s then (1 : ℤ) else 0)).trans
          (tuple_counts p d s)

set_option maxHeartbeats 0 in
theorem initial_counts (s : Fin 41 ⊕ (Fin 41 ⊕ Fin 41)) :
    (∑ r : Fin 5 → Fin 3, if cl (HardinA229590StripData.boundary r) 2 = s
      then (1 : ℤ) else 0) = initial s := by
  cases s with
  | inl j =>
    simpa only [cl, ↓reduceIte, Sum.inl.injEq, initial, Sum.elim_inl,
      HardinA229590StripData.cl, Nat.one_ne_zero] using
        HardinA229590StripCut.initial_counts (Sum.inl j)
  | inr s => simp [cl, initial]

end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripCut

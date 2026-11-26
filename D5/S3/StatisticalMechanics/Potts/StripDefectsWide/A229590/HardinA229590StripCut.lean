/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripCut
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripCut
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.finite_certificate
   digest: The one-defect extension of the five-row HA quotient. -/

/-
admission_basis: open-problem-resolution (#31329; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229590Strip.result)
column_boundary: proof_shape=bind-only; consumers=transition_counts
column_sum: proof_shape=bind-only; consumers=transition_counts, initial_counts
cross_zero: proof_shape=bind-only; consumers=tuple_counts
tuple_counts: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=bind-only; consumers=HardinA229590Strip.count_transfer
initial_counts: proof_shape=bind-only; consumers=HardinA229590Strip.count_transfer
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripNew

/-! Exact five-row one-defect class transfers and suffix counts. -/

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripCut
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open HardinA229590StripData
set_option maxRecDepth 100000
set_option Elab.async false

set_option maxHeartbeats 0 in
theorem column_boundary (r : Fin 5 → Fin 3) : column (boundary r) = r := by
  exact funext (column_grid 1 (fun p : Fin 5 × Fin 1 => r p.1) 0)

set_option maxHeartbeats 0 in
theorem column_sum (f : Col → ℤ) :
    (∑ r : Fin 5 → Fin 3, f (boundary r)) = ∑ c : Col, f c := by
  change (∑ r : Fin 5 → Fin 3, f (r 0,r 1,r 2,r 3,r 4)) = ∑ c : Col, f c
  simpa [Fintype.sum_prod_type] using
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip.label_sum
      (fun r => f (r 0,r 1,r 2,r 3,r 4))

set_option maxHeartbeats 0 in
private theorem cross_zero (a b : Col) :
    cross a (column b) = 0 ↔ compatible a b := by
  simp [cross, bondDefects, between, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, compatible]

set_option maxHeartbeats 0 in
private theorem tuple_counts (p : Col) (d : Fin 2) (s : Fin 41 ⊕ Fin 41) :
    (∑ c : Col, if cross p (column c) ≤ d.val ∧
      cl c (d.val - cross p (column c)) = s then (1 : ℤ) else 0) = T (cl p d.val) s := by
  fin_cases d
  · cases s with
    | inl j => simp [cl, T, Matrix.fromBlocks]
    | inr j =>
      change (∑ c : Col, if cross p (column c) ≤ 0 ∧
        cl c (0 - cross p (column c)) = Sum.inr j then (1 : ℤ) else 0) = Q (cls p) j
      simpa only [Fin.val_zero, Nat.le_zero, Nat.zero_sub, cl, ↓reduceIte,
        Sum.inr.injEq, cross_zero, T, Matrix.fromBlocks] using
          D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.quotient_rows p j
  · cases s with
    | inl j =>
      have cut (c : Col) :
          (cross p (column c) ≤ 1 ∧ cl c (1 - cross p (column c)) = Sum.inl j) ↔
            cross p (column c) = 0 ∧ cls c = j := by
        by_cases hc : cross p (column c) = 0
        · simp [hc, cl]
        · by_cases h : cross p (column c) ≤ 1
          · have he : cross p (column c) = 1 := by omega
            simp [he, cl]
          · simp [h, hc]
      change (∑ c : Col, if cross p (column c) ≤ 1 ∧
        cl c (1 - cross p (column c)) = Sum.inl j then (1 : ℤ) else 0) = Q (cls p) j
      simp_rw [cut, cross_zero]
      exact D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.quotient_rows p j
    | inr j =>
      have cut (c : Col) :
          (cross p (column c) ≤ 1 ∧ cl c (1 - cross p (column c)) = Sum.inr j) ↔
            cross p (column c) = 1 ∧ cls c = j := by
        by_cases hc : cross p (column c) = 1
        · simp [hc, cl]
        · by_cases h : cross p (column c) ≤ 1
          · have he : cross p (column c) = 0 := by omega
            simp [he, cl]
          · simp [h, hc]
      change (∑ c : Col, if cross p (column c) ≤ 1 ∧
        cl c (1 - cross p (column c)) = Sum.inr j then (1 : ℤ) else 0) = R (cls p) j
      simp_rw [cut]
      exact HardinA229590StripNew.quotient_rows p j

set_option maxHeartbeats 0 in
theorem transition_counts (p : Col) (d : Fin 2) (s : Fin 41 ⊕ Fin 41) :
    (∑ r : Fin 5 → Fin 3, if cross p r ≤ d.val ∧
      cl (boundary r) (d.val - cross p r) = s then (1 : ℤ) else 0) = T (cl p d.val) s := by
  calc
    _ = ∑ r : Fin 5 → Fin 3, if cross p (column (boundary r)) ≤ d.val ∧
        cl (boundary r) (d.val - cross p (column (boundary r))) = s
        then (1 : ℤ) else 0 := by simp_rw [column_boundary]
    _ = _ := (column_sum (fun c => if cross p (column c) ≤ d.val ∧
        cl c (d.val - cross p (column c)) = s then (1 : ℤ) else 0)).trans
          (tuple_counts p d s)

set_option maxHeartbeats 0 in
theorem initial_counts (s : Fin 41 ⊕ Fin 41) :
    (∑ r : Fin 5 → Fin 3, if cl (boundary r) 1 = s then (1 : ℤ) else 0) = initial s := by
  rw [column_sum (fun c => if cl c 1 = s then (1 : ℤ) else 0)]
  cases s with
  | inl j => simpa only [cl, Nat.one_ne_zero, ↓reduceIte, Sum.inl.injEq, initial,
      Sum.elim_inl] using initial_class_counts j
  | inr j => simp [cl, initial]

end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripCut

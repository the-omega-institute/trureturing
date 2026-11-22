/- GID: D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen
   generality: S
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed rank weights give a dimension sixteen single-coordinate budget lower bound. -/

import D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteen

open Finset
open D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor

noncomputable section

private def layer {V : Type*} [Fintype V] (rank : V → ℕ) (r : ℕ) : Finset V :=
  univ.filter fun a => rank a = r

private theorem subset_top (i : Fin 16) (A : AxisSubset 16 i) : A.val ⊆ (axisTop i).val :=
  fun j hj => mem_erase.mpr ⟨fun h => A.property (h ▸ hj), mem_univ j⟩

private theorem top_card (i : Fin 16) : (axisTop i).val.card = 15 := by
  unfold axisTop
  simp [Finset.card_erase_of_mem (mem_univ i)]

private theorem subset_layer_count (i : Fin 16) (r : ℕ) :
    (layer (fun A : AxisSubset 16 i => A.val.card) r).card = Nat.choose 15 r := by
  rw [← top_card i, ← card_powersetCard r (axisTop i).val]
  refine card_bij (fun A _ => A.val) ?_ ?_ ?_
  · intro A hA
    exact mem_powersetCard.mpr ⟨subset_top i A, (mem_filter.mp hA).2⟩
  · intro A _ B _ h
    exact Subtype.ext h
  · intro B hB
    obtain ⟨included, size⟩ := mem_powersetCard.mp hB
    have outside : i ∉ B := fun h => (axisTop i).property (included h)
    exact ⟨⟨B, outside⟩, mem_filter.mpr ⟨mem_univ _, size⟩, rfl⟩


private def rowWeight : ℕ → ℤ
  | 0 | 15 => -2
  | 1 | 2 => -1
  | 11 | 12 => 1
  | 13 | 14 => 2
  | _ => 0

private def colWeight : ℕ → ℤ
  | 0 | 1 => 2
  | 2 | 3 => 1
  | 12 | 13 => -1
  | 14 | 15 => -2
  | _ => 0

private def charge (a b : ℕ) : ℤ :=
  if a ≠ 15 ∧ a % 2 = 1 ∧ b % 2 = 1 then 1 else 0

private theorem weight_le_charge (a b : ℕ) (ha : a ≤ 15) (hb : b ≤ 15)
    (hs : a = 15 ∨ a ≤ b) :
    rowWeight a + colWeight b ≤ charge a b := by
  interval_cases a <;> interval_cases b <;> norm_num [rowWeight, colWeight, charge] at *

private def degreeCap (r : ℕ) : ℕ := if r = 15 then 2 else 3

private def degreeMin (r : ℕ) : ℕ := if r = 15 then 0 else 1

private def weightLower (w : ℤ) (r : ℕ) : ℤ :=
  w * (if 0 ≤ w then degreeMin r else degreeCap r : ℤ)

private theorem weighted_degree_bound (w : ℤ) (r d : ℕ)
    (lower : degreeMin r ≤ d) (upper : d ≤ degreeCap r) :
    weightLower w r ≤ w * d := by
  unfold weightLower
  split_ifs with hw
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast lower) hw
  · exact mul_le_mul_of_nonpos_left (by exact_mod_cast upper) (le_of_not_ge hw)

private theorem weighted_rank_sum {V : Type*} [Fintype V] (rank : V → ℕ)
    (count : ∀ r, (layer rank r).card = Nat.choose 15 r)
    (bounded : ∀ a, rank a ≤ 15) (w : ℕ → ℤ) :
    (∑ a, w (rank a)) = ∑ r ∈ range 16, w r * Nat.choose 15 r := by
  have regroup (r : ℕ) : (∑ a ∈ layer rank r, w (rank a)) =
      w r * Nat.choose 15 r := by
    calc
      _ = ∑ _a ∈ layer rank r, w r :=
        sum_congr rfl fun a ha => by rw [(mem_filter.mp ha).2]
      _ = _ := by rw [sum_const, nsmul_eq_mul, count, mul_comm]
  rw [← sum_congr (rfl : range 16 = range 16) (fun r _ => regroup r)]
  unfold layer
  rw [sum_fiberwise_eq_sum_filter]
  apply sum_congr _ fun _ _ => rfl
  ext a
  simp [bounded a, Nat.lt_succ_iff]

private theorem rank_cost_lower {V : Type*} [Fintype V] (rank : V → ℕ)
    (e : V → V → ℕ)
    (bounded : ∀ a, rank a ≤ 15) (count : ∀ r, (layer rank r).card = Nat.choose 15 r)
    (support : ∀ a b, e a b ≠ 0 → rank a = 15 ∨ rank a ≤ rank b)
    (rowMin : ∀ a, degreeMin (rank a) ≤ ∑ b, e a b)
    (rowCap : ∀ a, (∑ b, e a b) ≤ degreeCap (rank a))
    (colMin : ∀ b, degreeMin (rank b) ≤ ∑ a, e a b)
    (colCap : ∀ b, (∑ a, e a b) ≤ degreeCap (rank b)) :
    508 ≤ ∑ a, ∑ b, charge (rank a) (rank b) * (e a b : ℤ) := by
  have rowBound : (∑ a, weightLower (rowWeight (rank a)) (rank a)) ≤
      ∑ a, rowWeight (rank a) * ((∑ b, e a b : ℕ) : ℤ) :=
    sum_le_sum fun a _ => weighted_degree_bound _ _ _ (rowMin a) (rowCap a)
  have colBound : (∑ b, weightLower (colWeight (rank b)) (rank b)) ≤
      ∑ b, colWeight (rank b) * ((∑ a, e a b : ℕ) : ℤ) :=
    sum_le_sum fun b _ => weighted_degree_bound _ _ _ (colMin b) (colCap b)
  calc
    508 = (∑ a, weightLower (rowWeight (rank a)) (rank a)) +
        ∑ b, weightLower (colWeight (rank b)) (rank b) := by
      rw [weighted_rank_sum rank count bounded (fun r => weightLower (rowWeight r) r),
        weighted_rank_sum rank count bounded (fun r => weightLower (colWeight r) r)]
      decide
    _ ≤ (∑ a, rowWeight (rank a) * ((∑ b, e a b : ℕ) : ℤ)) +
        ∑ b, colWeight (rank b) * ((∑ a, e a b : ℕ) : ℤ) := add_le_add rowBound colBound
    _ = ∑ a, ∑ b, (rowWeight (rank a) + colWeight (rank b)) * (e a b : ℤ) := by
      simp_rw [Nat.cast_sum, mul_sum, add_mul, sum_add_distrib]
      rw [sum_comm (f := fun a b => colWeight (rank b) * (e a b : ℤ))]
    _ ≤ _ := sum_le_sum fun a _ => sum_le_sum fun b _ => by
      by_cases hz : e a b = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_right
          (weight_le_charge _ _ (bounded a) (bounded b) (support a b hz)) (by positivity)

private theorem full_rank_cost_ge_2036 (i : Fin 16) (e : AxisSubset 16 i → AxisSubset 16 i → ℕ)
    (support : ∀ A B, A ≠ axisTop i → e A B ≠ 0 → A.val ⊆ B.val)
    (rowMin : ∀ A ≠ axisTop i, 1 ≤ ∑ B, e A B)
    (colMin : ∀ B ≠ axisTop i, 1 ≤ ∑ A, e A B)
    (rowCap : ∀ A, (∑ B, e A B) ≤ if A = axisTop i then 2 else 3)
    (colCap : ∀ B, (∑ A, e A B) ≤ if B = axisTop i then 2 else 3) :
    2036 ≤ 4 * (1 + ∑ A, ∑ B, if A ≠ axisTop i ∧
      A.val.card % 2 = 1 ∧ B.val.card % 2 = 1 then e A B else 0) := by
  have ht (A : AxisSubset 16 i) : A.val.card = 15 ↔ A = axisTop i := by
    constructor
    · intro h
      apply Subtype.ext
      exact eq_of_subset_of_card_le (subset_top i A) (by rw [top_card i, h])
    · rintro rfl
      exact top_card i
  have hl := rank_cost_lower (fun A : AxisSubset 16 i => A.val.card) e
    (fun A => (card_le_card (subset_top i A)).trans_eq (top_card i))
    (subset_layer_count i)
    (fun A B h => by
      by_cases ha : A = axisTop i
      · exact Or.inl ((ht A).2 ha)
      · exact Or.inr (card_le_card (support A B ha h)))
    (fun A => by by_cases ha : A = axisTop i <;> simp [degreeMin, ht, ha, rowMin])
    (fun A => by simpa [degreeCap, ht] using rowCap A)
    (fun B => by by_cases hb : B = axisTop i <;> simp [degreeMin, ht, hb, colMin])
    (fun B => by simpa [degreeCap, ht] using colCap B)
  have hc (A B : AxisSubset 16 i) :
      charge A.val.card B.val.card * (e A B : ℤ) =
        ((if A ≠ axisTop i ∧ A.val.card % 2 = 1 ∧ B.val.card % 2 = 1
          then e A B else 0 : ℕ) : ℤ) := by
    unfold charge
    have agree : (A.val.card ≠ 15 ∧ A.val.card % 2 = 1 ∧ B.val.card % 2 = 1) ↔
        (A ≠ axisTop i ∧ A.val.card % 2 = 1 ∧ B.val.card % 2 = 1) :=
      and_congr (not_congr (ht A)) Iff.rfl
    by_cases h : A.val.card ≠ 15 ∧ A.val.card % 2 = 1 ∧ B.val.card % 2 = 1
    · simp only [ite_eq_left h, ite_eq_left (agree.mp h), one_mul]
    · simp only [ite_eq_right h, ite_eq_right (mt agree.mpr h), zero_mul, Nat.cast_zero]
  simp_rw [hc, ← Nat.cast_sum] at hl
  exact Nat.mul_le_mul_left 4 (Nat.add_le_add_left (by exact_mod_cast hl) 1)

open D5.S3.ConceptDynamics.Attribution.ParitySeedFactor

/-- At multiplier three, every feasible dimension sixteen single-coordinate budget is at least 2036. -/
theorem axis_budget_ge_2036 (i : Fin 16) (budget : ℕ) (feasible : axisFactorWithin 3 i budget) :
    2036 ≤ budget := by
  obtain ⟨edge, selected, _, _, row, col, support, cost⟩ := feasible
  let e (A B : AxisSubset 16 i) : ℕ := (edge A B).toNat
  have support' (A B : AxisSubset 16 i) (ha : A ≠ axisTop i) (h : e A B ≠ 0) :
      A.val ⊆ B.val := by
    apply support A B ha
    cases hEdge : edge A B
    · exact (h (by simp [e, hEdge])).elim
    · rfl
  have ordinary (d : ℕ) (h : residualDegree 3 selected false d) : 1 ≤ d := by
    have odd : d % 2 = 1 := by simpa [residualDegree] using h.2
    omega
  have cap (A : AxisSubset 16 i) (d : ℕ)
      (h : residualDegree 3 selected (decide (A = axisTop i)) d) :
      d ≤ if A = axisTop i then 2 else 3 := by
    by_cases ha : A = axisTop i
    · cases selected
      · have hd : d ≤ 1 := by simpa [ha, residualDegree] using h.1
        simp only [ha, ite_true]
        omega
      · simpa [ha, residualDegree] using h.1
    · simpa [ha, residualDegree] using h.1
  have bound := full_rank_cost_ge_2036 i e support'
    (fun A ha => ordinary _ (by simpa [e, ha] using row A))
    (fun B hb => ordinary _ (by simpa [e, hb] using col B))
    (fun A => cap A _ (row A))
    (fun B => cap B _ (col B))
  exact bound.trans cost

end
end D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteen

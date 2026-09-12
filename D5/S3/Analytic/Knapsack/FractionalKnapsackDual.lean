/- GID: D5/S3/Analytic/Knapsack/FractionalKnapsackDual
   generality: G
   mirror-B: D5/B/S3/Analytic/Knapsack/FractionalKnapsackDual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite fractional knapsack admits a greedy maximizer and an attaining nonnegative dual price. -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic

open scoped BigOperators

noncomputable section

namespace D5.S3.Analytic.Knapsack.FractionalKnapsackDual

variable {ι : Type*} [DecidableEq ι]

/-- Fill a list in order, stopping at the first item that exceeds the remaining budget. -/
def greedyFill (w : ι → ℝ) : List ι → ℝ → ι → ℝ
  | [], _ => fun _ => 0
  | a :: l, B => if w a ≤ B then
      Function.update (greedyFill w l (B - w a)) a 1
    else Function.update (fun _ => 0) a (B / w a)

/-- The box and budget constraints. -/
def Feasible [Fintype ι] (w : ι → ℝ) (B : ℝ) (t : ι → ℝ) : Prop :=
  (∀ i, t i ∈ Set.Icc 0 1) ∧ ∑ i, w i * t i ≤ B

/-- The finite linear return. -/
def objective [Fintype ι] (v t : ι → ℝ) : ℝ := ∑ i, v i * t i

/-- The upper bound obtained by pricing the budget and maximizing each box coordinate. -/
def dualValue [Fintype ι] (w v : ι → ℝ) (B λ : ℝ) : ℝ :=
  λ * B + ∑ i, max 0 (v i - λ * w i)

private theorem box_bound (c t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    c * t ≤ max 0 c := by
  rcases le_total 0 c with hc | hc
  · rw [max_eq_right hc]
    nlinarith [ht.2]
  · rw [max_eq_left hc]
    exact mul_nonpos_of_nonpos_of_nonneg hc ht.1

private theorem weak_duality [Fintype ι] (w v : ι → ℝ) (B λ : ℝ)
    (hλ : 0 ≤ λ) (t : ι → ℝ) (ht : Feasible w B t) :
    objective v t ≤ dualValue w v B λ := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => box_bound (v i - λ * w i) (t i) (ht.1 i))
  have hbudget := mul_le_mul_of_nonneg_left ht.2 hλ
  have hid : (∑ i, (v i - λ * w i) * t i) =
      objective v t - λ * ∑ i, w i * t i := by
    simp only [objective, sub_mul, Finset.sum_sub_distrib, mul_assoc,
      Finset.mul_sum]
  rw [hid] at hsum
  dsimp [dualValue]
  linarith

private structure GreedyData (w v : ι → ℝ) (B : ℝ)
    (s : Finset ι) (l : List ι) (λ : ℝ) : Prop where
  nodup : l.Nodup
  covers : l.toFinset = s
  sorted : l.Pairwise (fun i j => v j / w j ≤ v i / w i)
  price_nonneg : 0 ≤ λ
  price_source : λ = 0 ∨ ∃ i ∈ s, λ = v i / w i
  box : ∀ i ∈ s, greedyFill w l B i ∈ Set.Icc 0 1
  budget : (∑ i ∈ s, w i * greedyFill w l B i) ≤ B
  slack : λ * (B - ∑ i ∈ s, w i * greedyFill w l B i) = 0
  coordinate : ∀ i ∈ s,
    (v i - λ * w i) * greedyFill w l B i = max 0 (v i - λ * w i)

private theorem greedy_data (w v : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, 0 ≤ v i) (s : Finset ι) :
    ∀ B : ℝ, 0 ≤ B → ∃ l λ, GreedyData w v B s l λ := by
  induction s using Finset.induction_on_max_value (fun i => v i / w i) with
  | empty =>
    intro B hB
    refine ⟨[], 0, ?_⟩
    constructor <;> simp_all
  | insert a s ha hmax ih =>
    intro B hB
    by_cases hfit : w a ≤ B
    · obtain ⟨l, λ, h⟩ := ih (B - w a) (sub_nonneg.mpr hfit)
      have hal : a ∉ l := by
        intro hal
        exact ha (h.covers ▸ List.mem_toFinset.mpr hal)
      have hsorted : (a :: l).Pairwise (fun i j => v j / w j ≤ v i / w i) :=
        List.pairwise_cons.mpr ⟨fun i hi => hmax i (h.covers ▸ List.mem_toFinset.mpr hi),
          h.sorted⟩
      have hλ : λ ≤ v a / w a := by
        rcases h.price_source with hz | ⟨i, hi, rfl⟩
        · rw [hz]; exact div_nonneg (hv a) (hw a).le
        · exact hmax i hi
      have hcoef : 0 ≤ v a - λ * w a :=
        sub_nonneg.mpr ((le_div_iff₀ (hw a)).mp hλ)
      have hself : greedyFill w (a :: l) B a = 1 := by simp [greedyFill, hfit]
      have hother (i : ι) (hi : i ∈ s) :
          greedyFill w (a :: l) B i = greedyFill w l (B - w a) i := by
        have hia : i ≠ a := fun he => ha (he ▸ hi)
        simp [greedyFill, hfit, hia]
      have hsum : (∑ i ∈ insert a s, w i * greedyFill w (a :: l) B i) =
          w a + ∑ i ∈ s, w i * greedyFill w l (B - w a) i := by
        rw [Finset.sum_insert ha, hself, mul_one]
        congr 1
        exact Finset.sum_congr rfl (fun i hi => by rw [hother i hi])
      refine ⟨a :: l, λ, {
        nodup := List.nodup_cons.mpr ⟨hal, h.nodup⟩
        covers := by simp [h.covers]
        sorted := hsorted
        price_nonneg := h.price_nonneg
        price_source := ?_
        box := ?_
        budget := ?_
        slack := ?_
        coordinate := ?_ }⟩
      · rcases h.price_source with hz | ⟨i, hi, he⟩
        · exact Or.inl hz
        · exact Or.inr ⟨i, Finset.mem_insert_of_mem hi, he⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · rw [hself]; exact ⟨zero_le_one, le_rfl⟩
        · rw [hother i hi]; exact h.box i hi
      · rw [hsum]; linarith [h.budget]
      · rw [hsum]
        convert h.slack using 1 <;> ring
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · rw [hself, mul_one, max_eq_right hcoef]
        · rw [hother i hi]; exact h.coordinate i hi
    · obtain ⟨l, μ, h⟩ := ih 0 le_rfl
      have hal : a ∉ l := by
        intro hal
        exact ha (h.covers ▸ List.mem_toFinset.mpr hal)
      have hsorted : (a :: l).Pairwise (fun i j => v j / w j ≤ v i / w i) :=
        List.pairwise_cons.mpr ⟨fun i hi => hmax i (h.covers ▸ List.mem_toFinset.mpr hi),
          h.sorted⟩
      have hself : greedyFill w (a :: l) B a = B / w a := by
        simp [greedyFill, hfit]
      have hother (i : ι) (hi : i ∈ s) : greedyFill w (a :: l) B i = 0 := by
        have hia : i ≠ a := fun he => ha (he ▸ hi)
        simp [greedyFill, hfit, hia]
      have hsum : (∑ i ∈ insert a s, w i * greedyFill w (a :: l) B i) = B := by
        rw [Finset.sum_insert ha, hself]
        have hz : (∑ i ∈ s, w i * greedyFill w (a :: l) B i) = 0 :=
          Finset.sum_eq_zero (fun i hi => by rw [hother i hi, mul_zero])
        rw [hz, add_zero, mul_div_cancel₀ B (hw a).ne']
      refine ⟨a :: l, v a / w a, {
        nodup := List.nodup_cons.mpr ⟨hal, h.nodup⟩
        covers := by simp [h.covers]
        sorted := hsorted
        price_nonneg := div_nonneg (hv a) (hw a).le
        price_source := Or.inr ⟨a, Finset.mem_insert_self a s, rfl⟩
        box := ?_
        budget := hsum.le
        slack := by rw [hsum, sub_self, mul_zero]
        coordinate := ?_ }⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · rw [hself]
          exact ⟨div_nonneg hB (hw a).le,
            ((div_lt_one (hw a)).mpr (lt_of_not_ge hfit)).le⟩
        · rw [hother i hi]; exact ⟨le_rfl, zero_le_one⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · rw [div_mul_cancel₀ _ (hw a).ne', sub_self, zero_mul, max_self]
        · have hcoef : v i - (v a / w a) * w i ≤ 0 :=
            sub_nonpos.mpr ((div_le_iff₀ (hw i)).mp (hmax i hi))
          rw [hother i hi, mul_zero, max_eq_left hcoef]

#print axioms weak_duality
#print axioms greedy_data

end D5.S3.Analytic.Knapsack.FractionalKnapsackDual

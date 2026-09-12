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

#print axioms weak_duality

end D5.S3.Analytic.Knapsack.FractionalKnapsackDual

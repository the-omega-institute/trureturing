/- GID: D5/S3/PrimeGaps/PrimeGap186BudgetOptimality
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prove that Young-weight retuning cannot lower any of the 52 fixed-cap outer budgets by one rounding unit. -/

import D5.S3.PrimeGaps.PrimeGap186CertifiedLossBudget

/-!
The coefficients here are upper bounds from the fixed upstream tables, not values of physical
integrals. Optimality is restricted to these fixed coefficients and independent upward rounding
in units of 10^-12. It does not assert sharpness of an integral enclosure, a sieve optimum, or
an improved prime-gap bound.

An exact discriminant certificate proves a statement about every positive real Young weight;
no numerical square-root approximation or parameter search is trusted by the proof.
-/

namespace D5.S3.PrimeGaps.PrimeGap186BudgetOptimality

open D5.S3.PrimeGaps.PrimeGap186CertifiedLossBudget
open D5.S3.PrimeGaps.PrimeGap186ExactCertificateIndex

/-- Strict AM-GM consequence in polynomial form, avoiding square roots. -/
private theorem sum_gt_of_discriminant (x y t : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 ≤ t)
    (hdisc : t ^ 2 < 4 * x * y) : t < x + y := by
  by_contra h
  have hbound : x + y ≤ t := le_of_not_gt h
  have hprod : 0 ≤ (t - (x + y)) * (t + (x + y)) :=
    mul_nonneg (sub_nonneg.mpr hbound) (add_nonneg ht (add_nonneg hx hy))
  nlinarith [sq_nonneg (x - y)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Every outer row has its optimum strictly above the predecessor of its rounded budget. -/
theorem outer_discriminant_certified : ∀ r : OuterRowAddress,
    0 ≤ outerRootBound r ∧ 0 ≤ outerFaceBound r ∧
      0 ≤ outerBudget r - 1 / 10 ^ 12 ∧
      (outerBudget r - 1 / 10 ^ 12) ^ 2 <
        4 * outerRootBound r * outerFaceBound r := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- The 45 inner rounded budgets are also minimal for their fixed weighted upper bounds. -/
theorem inner_predecessor_certified : ∀ r : InnerRowAddress,
    innerBudget r - 1 / 10 ^ 12 < innerWeight r * innerMassBound r := by
  decide +kernel

/-- Any positive real Young weight stays above the preceding budget-grid point. -/
theorem outer_cost_gt_predecessor (r : OuterRowAddress) (q : ℝ) (hq : 0 < q) :
    (outerBudget r : ℝ) - 1 / 10 ^ 12 <
      q * (outerRootBound r : ℝ) + (outerFaceBound r : ℝ) / q := by
  have hc : 0 ≤ (outerRootBound r : ℝ) ∧ 0 ≤ (outerFaceBound r : ℝ) ∧
      0 ≤ (outerBudget r : ℝ) - 1 / 10 ^ 12 ∧
      ((outerBudget r : ℝ) - 1 / 10 ^ 12) ^ 2 <
        4 * (outerRootBound r : ℝ) * (outerFaceBound r : ℝ) := by
    have hcert := outer_discriminant_certified r
    have hbudget := (Rat.cast_nonneg (K := ℝ)).2 hcert.2.2.1
    have hdisc := (Rat.cast_lt (K := ℝ)).2 hcert.2.2.2
    push_cast at hbudget hdisc
    exact ⟨Rat.cast_nonneg.mpr hcert.1, Rat.cast_nonneg.mpr hcert.2.1, hbudget, hdisc⟩
  apply sum_gt_of_discriminant _ _ _
    (mul_nonneg hq.le hc.1) (div_nonneg hc.2.1 hq.le) hc.2.2.1
  calc
    ((outerBudget r : ℝ) - 1 / 10 ^ 12) ^ 2 <
        4 * (outerRootBound r : ℝ) * (outerFaceBound r : ℝ) := hc.2.2.2
    _ = 4 * (q * (outerRootBound r : ℝ)) * ((outerFaceBound r : ℝ) / q) := by
      field_simp [ne_of_gt hq] <;> ring

/-- Exact no-go certificate for reducing any independent rounded outer budget by retuning q. -/
theorem no_young_retuning_saves_one_unit (r : OuterRowAddress) (q : ℝ) (hq : 0 < q) :
    ¬ q * (outerRootBound r : ℝ) + (outerFaceBound r : ℝ) / q ≤
      (outerBudget r : ℝ) - 1 / 10 ^ 12 :=
  not_le_of_gt (outer_cost_gt_predecessor r q hq)

/-- The recorded budget is attainable with the existing weight and cannot be lowered to
its predecessor using any positive real weight, for the same pair of component upper bounds. -/
theorem outer_rounded_budget_optimal (r : OuterRowAddress) :
    (∃ q : ℝ, 0 < q ∧
      q * (outerRootBound r : ℝ) + (outerFaceBound r : ℝ) / q ≤ (outerBudget r : ℝ)) ∧
    (∀ q : ℝ, 0 < q →
      (outerBudget r : ℝ) - 1 / 10 ^ 12 <
        q * (outerRootBound r : ℝ) + (outerFaceBound r : ℝ) / q) := by
  constructor
  · refine ⟨(outerScale r : ℝ), ?_⟩
    exact_mod_cast outer_rounding_certified r
  · exact outer_cost_gt_predecessor r

/-- The recorded inner weighted cap lies in its last rounding interval. -/
theorem inner_rounded_budget_optimal (r : InnerRowAddress) :
    (innerBudget r : ℝ) - 1 / 10 ^ 12 <
        (innerWeight r : ℝ) * (innerMassBound r : ℝ) ∧
      (innerWeight r : ℝ) * (innerMassBound r : ℝ) ≤ (innerBudget r : ℝ) := by
  constructor
  · have hcast := (Rat.cast_lt (K := ℝ)).2 (inner_predecessor_certified r)
    push_cast at hcast
    exact hcast
  · exact_mod_cast (inner_rounding_certified r).2

#print axioms outer_discriminant_certified
#print axioms inner_predecessor_certified
#print axioms outer_cost_gt_predecessor
#print axioms no_young_retuning_saves_one_unit
#print axioms outer_rounded_budget_optimal
#print axioms inner_rounded_budget_optimal

end D5.S3.PrimeGaps.PrimeGap186BudgetOptimality

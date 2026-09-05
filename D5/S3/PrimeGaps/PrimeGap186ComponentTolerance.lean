/- GID: D5/S3/PrimeGaps/PrimeGap186ComponentTolerance
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Allocate a verified positive error allowance to all 149 physical components while preserving the strict numerical score margin. -/

import D5.S3.PrimeGaps.PrimeGap186CertifiedLossBudget

/-!
This is an alternative sufficient arithmetic certificate with explicit relaxed analytic
hypotheses. It neither proves a physical-integral inequality nor implies the original tighter
152-cell conjunction. A connection to the upstream analytic comparison theorem is still needed
before this interface could replace the upstream physical input.

For each outer row, the root allowance is delta/q and the face allowance is delta*q.
Each contributes at most delta to the weighted loss. Each inner row receives allowance delta/w.
All constants are derived from the existing table owner; there is no second coefficient table.
-/

namespace D5.S3.PrimeGaps.PrimeGap186ComponentTolerance

open D5.S3.PrimeGaps.PrimeGap186CertifiedLossBudget
open D5.S3.PrimeGaps.PrimeGap186ExactCertificateIndex
open scoped BigOperators

/-- Weighted loss allowance per physical component. -/
def componentAllowance : ℚ := 1 / 20000000

def relaxedRootBound (r : OuterRowAddress) : ℚ :=
  outerRootBound r + componentAllowance / outerScale r

def relaxedFaceBound (r : OuterRowAddress) : ℚ :=
  outerFaceBound r + componentAllowance * outerScale r

def relaxedMassBound (r : InnerRowAddress) : ℚ :=
  innerMassBound r + componentAllowance / innerWeight r

def relaxedOuterBudget (r : OuterRowAddress) : ℚ := outerBudget r + 2 * componentAllowance
def relaxedInnerBudget (r : InnerRowAddress) : ℚ := innerBudget r + componentAllowance

/-- Exact checks simultaneously certify strict relaxation and the two-component row budget. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem relaxed_outer_certified : ∀ r : OuterRowAddress,
    outerRootBound r < relaxedRootBound r ∧
    outerFaceBound r < relaxedFaceBound r ∧
    outerScale r * relaxedRootBound r + relaxedFaceBound r / outerScale r ≤
      relaxedOuterBudget r := by
  decide

/-- Every inner cap is strictly relaxed, with only delta additional weighted loss. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem relaxed_inner_certified : ∀ r : InnerRowAddress,
    0 < innerWeight r ∧ innerMassBound r < relaxedMassBound r ∧
    innerWeight r * relaxedMassBound r ≤ relaxedInnerBudget r := by
  decide

def totalRelaxedBudget : ℚ :=
  (∑ r : OuterRowAddress, relaxedOuterBudget r) +
    ∑ r : InnerRowAddress, relaxedInnerBudget r

/-- There are 149 weighted components, not 97 inequalities. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem totalRelaxedBudget_eq :
    totalRelaxedBudget = totalRoundedBudget + 149 / 20000000 := by
  decide

/-- The explicit allocation fits within the loss allowance preserving the strict margin. -/
theorem totalRelaxedBudget_le_safe :
    totalRelaxedBudget ≤ totalRoundedBudget + 1 / 100000 := by
  rw [totalRelaxedBudget_eq]
  linarith

/-- Real soundness of the relaxed row certificate. All 149 analytic bounds are hypotheses. -/
theorem totalLoss_le_relaxedBudget (root face : OuterRowAddress → ℝ)
    (mass : InnerRowAddress → ℝ)
    (hroot : ∀ r, root r ≤ (relaxedRootBound r : ℝ))
    (hface : ∀ r, face r ≤ (relaxedFaceBound r : ℝ))
    (hmass : ∀ r, mass r ≤ (relaxedMassBound r : ℝ)) :
    totalLoss root face mass ≤ (totalRelaxedBudget : ℝ) := by
  have ho :
      (∑ r : OuterRowAddress,
        (outerScale r : ℝ) * root r + face r / (outerScale r : ℝ)) ≤
      ∑ r : OuterRowAddress, (relaxedOuterBudget r : ℝ) := by
    apply Finset.sum_le_sum
    intro r _
    have hq : 0 ≤ (outerScale r : ℝ) := by
      exact_mod_cast (outer_rounding_certified r).1.le
    have hr : (outerScale r : ℝ) * (relaxedRootBound r : ℝ) +
        (relaxedFaceBound r : ℝ) / (outerScale r : ℝ) ≤ (relaxedOuterBudget r : ℝ) := by
      exact_mod_cast (relaxed_outer_certified r).2.2
    exact (add_le_add (mul_le_mul_of_nonneg_left (hroot r) hq)
      (div_le_div_of_nonneg_right (hface r) hq)).trans hr
  have hi :
      (∑ r : InnerRowAddress, (innerWeight r : ℝ) * mass r) ≤
      ∑ r : InnerRowAddress, (relaxedInnerBudget r : ℝ) := by
    apply Finset.sum_le_sum
    intro r _
    have hw : 0 ≤ (innerWeight r : ℝ) := by
      exact_mod_cast (relaxed_inner_certified r).1.le
    have hr : (innerWeight r : ℝ) * (relaxedMassBound r : ℝ) ≤
        (relaxedInnerBudget r : ℝ) := by
      exact_mod_cast (relaxed_inner_certified r).2.2
    exact (mul_le_mul_of_nonneg_left (hmass r) hw).trans hr
  calc
    totalLoss root face mass ≤
        (∑ r : OuterRowAddress, (relaxedOuterBudget r : ℝ)) +
          ∑ r : InnerRowAddress, (relaxedInnerBudget r : ℝ) := add_le_add ho hi
    _ = (totalRelaxedBudget : ℝ) := by
      unfold totalRelaxedBudget
      push_cast <;> rfl

/-- The relaxed 149-component caps and unchanged three scalar endpoints suffice for the
strict arithmetic score margin. This does not discharge any analytic hypothesis. -/
theorem strict_score_of_relaxed_component_bounds
    (root face : OuterRowAddress → ℝ) (mass : InnerRowAddress → ℝ) (I J : ℝ)
    (hroot : ∀ r, root r ≤ (relaxedRootBound r : ℝ))
    (hface : ∀ r, face r ≤ (relaxedFaceBound r : ℝ))
    (hmass : ∀ r, mass r ≤ (relaxedMassBound r : ℝ))
    (hIlower : (recordedILower : ℝ) ≤ I)
    (hIupper : I ≤ (recordedIUpper : ℝ))
    (hJlower : (recordedJLower : ℝ) ≤ J) :
    1 + 1 / 50000 < (rhoStar : ℝ) * (J / I - totalLoss root face mass) := by
  apply score_gt_strict_margin_of_aggregate_loss I J _ hIlower hIupper hJlower
  have hbudget : (totalRelaxedBudget : ℝ) ≤ (totalRoundedBudget : ℝ) + 1 / 100000 := by
    exact_mod_cast totalRelaxedBudget_le_safe
  exact (totalLoss_le_relaxedBudget root face mass hroot hface hmass).trans hbudget

#print axioms relaxed_outer_certified
#print axioms relaxed_inner_certified
#print axioms totalRelaxedBudget_eq
#print axioms totalRelaxedBudget_le_safe
#print axioms totalLoss_le_relaxedBudget
#print axioms strict_score_of_relaxed_component_bounds

end D5.S3.PrimeGaps.PrimeGap186ComponentTolerance

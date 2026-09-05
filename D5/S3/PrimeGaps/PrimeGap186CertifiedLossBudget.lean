/- GID: D5/S3/PrimeGaps/PrimeGap186CertifiedLossBudget
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Replay all 97 weighted rounding checks and prove quantitative additional-loss allowances for the conditional sieve score. -/

import D5.S3.PrimeGaps.PrimeGap186PhysicalBoundTables
import D5.S3.PrimeGaps.PrimeGap186ExactCertificateIndex

/-!
Source constants: openai/PrimeGaps186, 61340d0b74163003b32756bb16e91d9209a5e330.

The finite arithmetic proved here is distinct from the 152 physical-integral inequalities.
Actual root, face, inner-mass and scalar values remain explicit real-valued inputs.
No theorem in this file proves an integral bound, DHL[40,2], or a prime-gap record.

The numerical content is the exact replay of every weighted rounding inequality and an
explicit loss headroom. The stronger certificate preserves a score above 1 + 1/50000,
allowing additional normalized loss 1/100000. A weaker certificate preserves a score above
one with additional loss 1/12500. Neither substitutes for the upstream analytic proof.
-/

namespace D5.S3.PrimeGaps.PrimeGap186CertifiedLossBudget

open D5.S3.PrimeGaps.PrimeGap186PhysicalBoundTables
open D5.S3.PrimeGaps.PrimeGap186ExactCertificateIndex
open D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGeometry
open scoped BigOperators

/-- Typed lookup preserves the existing integer tables as the sole data owner. -/
def outerRowData : OuterRowAddress → OuterBoundRow
  | .orderTwo j => outerOrderTwoBounds.get j
  | .orderFiveHalves j => outerOrderFiveHalvesBounds.get j

def innerRowData : InnerRowAddress → InnerBoundRow
  | .oldOrderTwo j => innerBaseOrderTwoBounds.get j
  | .oldOrderFiveHalves j => innerBaseOrderFiveHalvesBounds.get j
  | .newOrderTwo j => innerEnlargedOrderTwoBounds.get j
  | .newOrderFiveHalves j => innerEnlargedOrderFiveHalvesBounds.get j

def outerScale (r : OuterRowAddress) : ℚ := (outerRowData r).1 / 10 ^ 6
def outerRootBound (r : OuterRowAddress) : ℚ := (outerRowData r).2.1 / 10 ^ 18
def outerFaceBound (r : OuterRowAddress) : ℚ := (outerRowData r).2.2.1 / 10 ^ 18
def outerBudget (r : OuterRowAddress) : ℚ := (outerRowData r).2.2.2 / 10 ^ 12

def innerMassBound (r : InnerRowAddress) : ℚ := (innerRowData r).1 / 10 ^ 18
def innerBudget (r : InnerRowAddress) : ℚ := (innerRowData r).2 / 10 ^ 12

/-- Restoration coefficients 1-a-b and 1-b, including the negative tail coefficient b. -/
def innerWeight : InnerRowAddress → ℚ
  | .oldOrderTwo _ | .oldOrderFiveHalves _ =>
      1 - 2479900401 / 2500000000 + 843183 / 1000000000
  | .newOrderTwo _ | .newOrderFiveHalves _ => 1 + 843183 / 1000000000

-- Finite rational calculations are replayed with decide, not native_decide.
-- Increased reduction depth accommodates the explicit 52-row enumeration.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- All 52 outer Young-weight budgets are valid, including the inverse-weight term. -/
theorem outer_rounding_certified : ∀ r : OuterRowAddress,
    0 < outerScale r ∧
      outerScale r * outerRootBound r + outerFaceBound r / outerScale r ≤ outerBudget r := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- All 45 inner weighted budgets are valid with the source's signed-hybrid coefficients. -/
theorem inner_rounding_certified : ∀ r : InnerRowAddress,
    0 ≤ innerWeight r ∧ innerWeight r * innerMassBound r ≤ innerBudget r := by
  decide

def totalRoundedBudget : ℚ :=
  (∑ r : OuterRowAddress, outerBudget r) + ∑ r : InnerRowAddress, innerBudget r

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- The complete rounded loss budget, obtained from the actual typed table entries. -/
theorem totalRoundedBudget_eq : totalRoundedBudget = 696075110 / 10 ^ 12 := by
  decide

/-- Linear normalized loss assembled from arbitrary real-valued physical components. -/
noncomputable def totalLoss (root face : OuterRowAddress → ℝ)
    (mass : InnerRowAddress → ℝ) : ℝ :=
  (∑ r : OuterRowAddress,
    (outerScale r : ℝ) * root r + face r / (outerScale r : ℝ)) +
  ∑ r : InnerRowAddress, (innerWeight r : ℝ) * mass r

/-- Soundness of row-budget aggregation. Each analytic bound is an explicit hypothesis. -/
theorem totalLoss_le_recordedBudget (root face : OuterRowAddress → ℝ)
    (mass : InnerRowAddress → ℝ)
    (hroot : ∀ r, root r ≤ (outerRootBound r : ℝ))
    (hface : ∀ r, face r ≤ (outerFaceBound r : ℝ))
    (hmass : ∀ r, mass r ≤ (innerMassBound r : ℝ)) :
    totalLoss root face mass ≤ (totalRoundedBudget : ℝ) := by
  have ho :
      (∑ r : OuterRowAddress,
        (outerScale r : ℝ) * root r + face r / (outerScale r : ℝ)) ≤
      ∑ r : OuterRowAddress, (outerBudget r : ℝ) := by
    apply Finset.sum_le_sum
    intro r _
    have hr : 0 < (outerScale r : ℝ) ∧
        (outerScale r : ℝ) * (outerRootBound r : ℝ) +
          (outerFaceBound r : ℝ) / (outerScale r : ℝ) ≤ (outerBudget r : ℝ) := by
      exact_mod_cast outer_rounding_certified r
    exact (add_le_add
      (mul_le_mul_of_nonneg_left (hroot r) hr.1.le)
      (div_le_div_of_nonneg_right (hface r) hr.1.le)).trans hr.2
  have hi :
      (∑ r : InnerRowAddress, (innerWeight r : ℝ) * mass r) ≤
      ∑ r : InnerRowAddress, (innerBudget r : ℝ) := by
    apply Finset.sum_le_sum
    intro r _
    have hr : 0 ≤ (innerWeight r : ℝ) ∧
        (innerWeight r : ℝ) * (innerMassBound r : ℝ) ≤ (innerBudget r : ℝ) := by
      exact_mod_cast inner_rounding_certified r
    exact (mul_le_mul_of_nonneg_left (hmass r) hr.1).trans hr.2
  calc
    totalLoss root face mass ≤
        (∑ r : OuterRowAddress, (outerBudget r : ℝ)) +
          ∑ r : InnerRowAddress, (innerBudget r : ℝ) := add_le_add ho hi
    _ = (totalRoundedBudget : ℝ) := by
      unfold totalRoundedBudget
      push_cast
      rfl

/-- Effective source density after its exact safety decrement. -/
def rhoStar : ℚ := physicalSourceRho - 1 / 10000000

/-- Recorded scalar endpoints. These definitions do not assert bounds on any integral. -/
def recordedILower : ℚ := 23685317816 / 10 ^ 24
def recordedIUpper : ℚ := 23685317890 / 10 ^ 24
def recordedJLower : ℚ := 90248755123 / 10 ^ 24

/-- Exact arithmetic margin of the recorded data after all rounded losses. -/
theorem recorded_score_margin :
    rhoStar * (recordedJLower / recordedIUpper - totalRoundedBudget) - 1 =
      55329972518846778463969 / 2368531789000000000000000000 := by
  rw [totalRoundedBudget_eq]
  decide

/-- The baseline arithmetic margin is strictly greater than 2 * 10^-5. -/
theorem recorded_score_margin_gt :
    1 + 1 / 50000 < rhoStar * (recordedJLower / recordedIUpper - totalRoundedBudget) := by
  rw [totalRoundedBudget_eq]
  norm_num [rhoStar, physicalSourceRho, recordedJLower, recordedIUpper]

/-- An additional normalized loss of 8 * 10^-5 still leaves a strict score above one. -/
theorem recorded_additional_loss_is_safe :
    1 < rhoStar *
      (recordedJLower / recordedIUpper - (totalRoundedBudget + 1 / 12500)) := by
  rw [totalRoundedBudget_eq]
  norm_num [rhoStar, physicalSourceRho, recordedJLower, recordedIUpper]

/-- Additional loss 10^-5 preserves the stronger 2 * 10^-5 score margin. -/
theorem recorded_strict_margin_is_safe :
    1 + 1 / 50000 < rhoStar *
      (recordedJLower / recordedIUpper - (totalRoundedBudget + 1 / 100000)) := by
  rw [totalRoundedBudget_eq]
  decide

/-- Transfer an exact rational threshold certificate to arbitrary real data meeting the
three recorded scalar endpoints and an aggregate loss bound. -/
theorem score_gt_of_aggregate_loss (extra threshold : ℚ)
    (hsafe : threshold < rhoStar *
      (recordedJLower / recordedIUpper - (totalRoundedBudget + extra)))
    (I J loss : ℝ)
    (hIlower : (recordedILower : ℝ) ≤ I)
    (hIupper : I ≤ (recordedIUpper : ℝ))
    (hJlower : (recordedJLower : ℝ) ≤ J)
    (hloss : loss ≤ (totalRoundedBudget : ℝ) + (extra : ℝ)) :
    (threshold : ℝ) < (rhoStar : ℝ) * (J / I - loss) := by
  have hI : 0 < I :=
    (by norm_num [recordedILower] : 0 < (recordedILower : ℝ)).trans_le hIlower
  have hU : 0 < (recordedIUpper : ℝ) := by norm_num [recordedIUpper]
  have hJ : 0 ≤ (recordedJLower : ℝ) := by norm_num [recordedJLower]
  have hρ : 0 ≤ (rhoStar : ℝ) := by norm_num [rhoStar, physicalSourceRho]
  have hratio : (recordedJLower : ℝ) / (recordedIUpper : ℝ) ≤ J / I := by
    apply (div_le_div_iff₀ hU hI).2
    calc
      (recordedJLower : ℝ) * I ≤
          (recordedJLower : ℝ) * (recordedIUpper : ℝ) :=
        mul_le_mul_of_nonneg_left hIupper hJ
      _ ≤ J * (recordedIUpper : ℝ) :=
        mul_le_mul_of_nonneg_right hJlower hU.le
  have hsafe' : (threshold : ℝ) < (rhoStar : ℝ) *
      ((recordedJLower : ℝ) / (recordedIUpper : ℝ) -
        ((totalRoundedBudget : ℝ) + (extra : ℝ))) := by
    exact_mod_cast hsafe
  exact hsafe'.trans_le (mul_le_mul_of_nonneg_left (sub_le_sub hratio hloss) hρ)

/-- Aggregate sufficiency for a score above one with additional loss 8 * 10^-5. -/
theorem score_gt_one_of_aggregate_loss (I J loss : ℝ)
    (hIlower : (recordedILower : ℝ) ≤ I)
    (hIupper : I ≤ (recordedIUpper : ℝ))
    (hJlower : (recordedJLower : ℝ) ≤ J)
    (hloss : loss ≤ (totalRoundedBudget : ℝ) + 1 / 12500) :
    1 < (rhoStar : ℝ) * (J / I - loss) := by
  simpa using score_gt_of_aggregate_loss (1 / 12500) 1
    recorded_additional_loss_is_safe I J loss hIlower hIupper hJlower hloss

/-- Aggregate sufficiency retaining the stronger margin used by the numerical comparison. -/
theorem score_gt_strict_margin_of_aggregate_loss (I J loss : ℝ)
    (hIlower : (recordedILower : ℝ) ≤ I)
    (hIupper : I ≤ (recordedIUpper : ℝ))
    (hJlower : (recordedJLower : ℝ) ≤ J)
    (hloss : loss ≤ (totalRoundedBudget : ℝ) + 1 / 100000) :
    1 + 1 / 50000 < (rhoStar : ℝ) * (J / I - loss) := by
  simpa using score_gt_of_aggregate_loss (1 / 100000) (1 + 1 / 50000)
    recorded_strict_margin_is_safe I J loss hIlower hIupper hJlower hloss

/-- Full typed conditional arithmetic assembly. The 149 component caps and three scalar
endpoints remain hypotheses, not axioms or conclusions. -/
theorem score_gt_one_with_additional_loss
    (root face : OuterRowAddress → ℝ) (mass : InnerRowAddress → ℝ)
    (I J extra : ℝ)
    (hroot : ∀ r, root r ≤ (outerRootBound r : ℝ))
    (hface : ∀ r, face r ≤ (outerFaceBound r : ℝ))
    (hmass : ∀ r, mass r ≤ (innerMassBound r : ℝ))
    (hIlower : (recordedILower : ℝ) ≤ I)
    (hIupper : I ≤ (recordedIUpper : ℝ))
    (hJlower : (recordedJLower : ℝ) ≤ J)
    (hextra : extra ≤ 1 / 12500) :
    1 < (rhoStar : ℝ) * (J / I - (totalLoss root face mass + extra)) := by
  apply score_gt_one_of_aggregate_loss I J _ hIlower hIupper hJlower
  exact add_le_add (totalLoss_le_recordedBudget root face mass hroot hface hmass) hextra

#print axioms outer_rounding_certified
#print axioms inner_rounding_certified
#print axioms totalRoundedBudget_eq
#print axioms totalLoss_le_recordedBudget
#print axioms recorded_score_margin
#print axioms recorded_score_margin_gt
#print axioms recorded_additional_loss_is_safe
#print axioms recorded_strict_margin_is_safe
#print axioms score_gt_of_aggregate_loss
#print axioms score_gt_one_of_aggregate_loss
#print axioms score_gt_strict_margin_of_aggregate_loss
#print axioms score_gt_one_with_additional_loss

end D5.S3.PrimeGaps.PrimeGap186CertifiedLossBudget

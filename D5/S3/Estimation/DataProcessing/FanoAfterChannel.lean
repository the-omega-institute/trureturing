/- GID: D5/S3/Estimation/DataProcessing/FanoAfterChannel
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/FanoAfterChannel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Combine finite Fano inversion with Markov data processing and channel garbling. -/

import D5.S3.Entropy.MutualInformationSymm
import D5.S3.Entropy.Submodularity.MarkovDataProcessing
import D5.S3.Estimation.FanoErrorBound

/-!
# Fano bounds after a finite channel

This module composes the uniform-prior Fano estimator bound with mutual-information data
processing. The first theorem accepts the repository's raw, division-free Markov identity. The
second verifies that identity for a nonnegative row-stochastic channel and transports the law,
prior, and mutual-information budget through the generated three-variable joint distribution.
-/

namespace D5.S3.Estimation.DataProcessing.FanoAfterChannel

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationSymm
open D5.S3.Entropy.Submodularity.StrongSubadditivity
open D5.S3.Entropy.Submodularity.MarkovDataProcessing
open D5.S3.Estimation.FanoErrorBound

open Classical in
/-- Uniform-prior Fano after a Markov garbling: every estimator from `Z` pays the information
budget available at the intermediate observation `Y`. -/
theorem fano_error_probability_lower_bound_of_markov
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (p : X × (Y × Z) → ℝ) (g : Z → X)
    (hp : (∀ q, 0 ≤ p q) ∧ ∑ q, p q = 1)
    (hmarkov : ∀ x y z, p (x, (y, z)) * marginal (yFirstLaw p) y =
      xyProjection p (x, y) * xzProjection (yFirstLaw p) (y, z))
    (huniform : marginal p = fun _ ↦ (Fintype.card X : ℝ)⁻¹)
    (hX : 2 ≤ Fintype.card X) :
    1 - (mutualInformation (xyProjection p) + Real.log 2) /
        Real.log (Fintype.card X) ≤
      ∑ q : X × Z, if g q.2 ≠ q.1 then xzProjection p q else 0 := by
  let pZX : Z × X → ℝ := fun q ↦ xzProjection p (q.2, q.1)
  have hpZX : (∀ q, 0 ≤ pZX q) ∧ ∑ q, pZX q = 1 := by
    constructor
    · intro q
      exact Finset.sum_nonneg fun y _ ↦ hp.1 (q.2, (y, q.1))
    · rw [← hp.2]
      simp only [pZX, xzProjection, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
  have huniformZX :
      marginal (fun q : X × Z ↦ pZX (q.2, q.1)) =
        fun _ ↦ (Fintype.card X : ℝ)⁻¹ := by
    change marginal (xzProjection p) = fun _ ↦ (Fintype.card X : ℝ)⁻¹
    rw [← huniform]
    funext x
    simp only [marginal, xzProjection, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  have hfano := fano_error_probability_lower_bound_uniform pZX g hpZX hX huniformZX
  have hmiSwap : mutualInformation pZX = mutualInformation (xzProjection p) := by
    simpa only [pZX] using mutual_information_symm (xzProjection p)
  have herrorSwap :
      (∑ q : Z × X, if g q.1 ≠ q.2 then pZX q else 0) =
        ∑ q : X × Z, if g q.2 ≠ q.1 then xzProjection p q else 0 := by
    simp only [pZX, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  rw [hmiSwap, herrorSwap] at hfano
  have hdpi := mutual_information_le_of_markov p hp hmarkov
  have hcard_gt_one : 1 < Fintype.card X := by omega
  have hcard_real_gt_one : (1 : ℝ) < Fintype.card X := by exact_mod_cast hcard_gt_one
  have hlog_pos : 0 < Real.log (Fintype.card X) := Real.log_pos hcard_real_gt_one
  have hquotient :
      (mutualInformation (xzProjection p) + Real.log 2) / Real.log (Fintype.card X) ≤
        (mutualInformation (xyProjection p) + Real.log 2) /
          Real.log (Fintype.card X) :=
    (div_le_div_iff_of_pos_right hlog_pos).2 (add_le_add hdpi le_rfl)
  linarith

open Classical in
/-- A nonnegative row-stochastic channel preserves a uniform hidden prior and subjects every
output estimator to the Fano floor determined by the pre-channel mutual information. -/
theorem fano_error_probability_lower_bound_after_channel
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (pXY : X × Y → ℝ) (W : Y → Z → ℝ) (g : Z → X)
    (hpXY : (∀ q, 0 ≤ pXY q) ∧ ∑ q, pXY q = 1)
    (hW_nonneg : ∀ y z, 0 ≤ W y z) (hW_sum : ∀ y, ∑ z, W y z = 1)
    (huniform : marginal pXY = fun _ ↦ (Fintype.card X : ℝ)⁻¹)
    (hX : 2 ≤ Fintype.card X) :
    1 - (mutualInformation pXY + Real.log 2) / Real.log (Fintype.card X) ≤
      ∑ q : X × Z, if g q.2 ≠ q.1 then
        xzProjection
          (fun r : X × (Y × Z) ↦ pXY (r.1, r.2.1) * W r.2.1 r.2.2) q else 0 := by
  let p : X × (Y × Z) → ℝ := fun q ↦ pXY (q.1, q.2.1) * W q.2.1 q.2.2
  have hp : (∀ q, 0 ≤ p q) ∧ ∑ q, p q = 1 := by
    constructor
    · intro q
      exact mul_nonneg (hpXY.1 _) (hW_nonneg _ _)
    · rw [← hpXY.2]
      simp only [p, Fintype.sum_prod_type, ← Finset.mul_sum, hW_sum, mul_one]
  have hp_uniform : marginal p = fun _ ↦ (Fintype.card X : ℝ)⁻¹ := by
    rw [← huniform]
    funext x
    simp only [marginal, p, Fintype.sum_prod_type, ← Finset.mul_sum, hW_sum, mul_one]
  have hxy : xyProjection p = pXY := by
    funext q
    simp only [xyProjection, p, ← Finset.mul_sum, hW_sum, mul_one]
  have hmarkov : ∀ x y z, p (x, (y, z)) * marginal (yFirstLaw p) y =
      xyProjection p (x, y) * xzProjection (yFirstLaw p) (y, z) := by
    simpa only [p] using markov_of_channel pXY W hW_sum
  have hbound :=
    fano_error_probability_lower_bound_of_markov p g hp hmarkov hp_uniform hX
  rw [hxy] at hbound
  simpa only [p] using hbound

#print axioms fano_error_probability_lower_bound_of_markov
#print axioms fano_error_probability_lower_bound_after_channel

end D5.S3.Estimation.DataProcessing.FanoAfterChannel

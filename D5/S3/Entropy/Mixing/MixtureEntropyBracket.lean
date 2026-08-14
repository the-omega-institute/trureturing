/- GID: D5/S3/Entropy/Mixing/MixtureEntropyBracket
   generality: G
   mirror-B: D5/B/S3/Entropy/Mixing/MixtureEntropyBracket
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bracket mixture entropy; upper equality via pairwise disjoint supports is not covered. -/

/- Library-search audit trail (2026-08-15):
   * Repository search covered mixture-entropy names, weighted entropy sums, and finite joint-law
     constructions throughout `D5/`; no existing mixture entropy bracket was found.
   * The pinned finite entropy API already supplies the exact ingredients: the entropy chain rule,
     conditioning reduction, conditional-entropy nonnegativity, entropy under coordinate swap, the
     entropy expression for mutual information, and vanishing mutual information exactly at product
     laws. The proofs below compose those declarations rather than re-proving their scalar cores.
   * The mixture joint law has cells `w i * q i j`. A zero weight makes both its conditional-entropy
     term and the corresponding weighted component entropy vanish, so no support restriction is
     needed. Units are nats because `shannonEntropy` uses `Real.log`.
-/

import D5.S3.Entropy.ConditioningReducesEntropy
import D5.S3.Entropy.EntropyNonneg
import D5.S3.Entropy.MutualInformationIndependence
import D5.S3.Entropy.MutualInformationSymm

namespace D5.S3.Entropy.Mixing.MixtureEntropyBracket

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.ConditioningReducesEntropy
open D5.S3.Entropy.EntropyNonneg
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationEntropy
open D5.S3.Entropy.MutualInformationIndependence
open D5.S3.Entropy.MutualInformationSymm

/-- The weighted mixture of a finite family of mass functions. -/
noncomputable def mixture {ι κ : Type*} [Fintype ι]
    (w : ι → ℝ) (q : ι → κ → ℝ) (j : κ) : ℝ :=
  ∑ i, w i * q i j

/-- The joint mass function whose first coordinate selects a mixture component. -/
def mixtureJoint {ι κ : Type*} (w : ι → ℝ) (q : ι → κ → ℝ) (z : ι × κ) : ℝ :=
  w z.1 * q z.1 z.2

/-- The first marginal of the mixture joint law is its weight law. -/
theorem mixtureJoint_marginal_eq_weight {ι κ : Type*} [Fintype κ]
    (w : ι → ℝ) (q : ι → κ → ℝ) (hq : ∀ i, ∑ j, q i j = 1) :
    marginal (mixtureJoint w q) = w := by
  funext i
  simp only [marginal, mixtureJoint]
  rw [← Finset.mul_sum, hq i, mul_one]

/-- The second marginal of the mixture joint law is the weighted mixture. -/
theorem mixtureJoint_swapped_marginal_eq_mixture {ι κ : Type*} [Fintype ι]
    (w : ι → ℝ) (q : ι → κ → ℝ) :
    marginal (fun z : κ × ι => mixtureJoint w q (z.2, z.1)) = mixture w q := by
  rfl

/-- Conditional entropy of the mixture joint law is weighted component entropy. -/
theorem mixtureJoint_conditionalEntropy_eq_weighted {ι κ : Type*}
    [Fintype ι] [Fintype κ] (w : ι → ℝ) (q : ι → κ → ℝ)
    (hq : ∀ i, ∑ j, q i j = 1) :
    conditionalEntropy (mixtureJoint w q) = ∑ i, w i * shannonEntropy (q i) := by
  classical
  rw [conditionalEntropy]
  apply Finset.sum_congr rfl
  intro i _
  rw [mixtureJoint_marginal_eq_weight w q hq]
  by_cases hwi : w i = 0
  · simp [hwi]
  · have hconditional : conditional (mixtureJoint w q) i = q i := by
      funext j
      simp [conditional, mixtureJoint, mixtureJoint_marginal_eq_weight w q hq, hwi]
    rw [hconditional]

private theorem mixtureJoint_nonneg {ι κ : Type*} (w : ι → ℝ) (q : ι → κ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hq : ∀ i j, 0 ≤ q i j) :
    ∀ z, 0 ≤ mixtureJoint w q z := by
  intro z
  exact mul_nonneg (hw z.1) (hq z.1 z.2)

private theorem mixtureJoint_sum_eq_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (q : ι → κ → ℝ) (hw : ∑ i, w i = 1)
    (hq : ∀ i, ∑ j, q i j = 1) :
    ∑ z, mixtureJoint w q z = 1 := by
  simp only [mixtureJoint, Fintype.sum_prod_type]
  calc
    (∑ i, ∑ j, w i * q i j) = ∑ i, w i * ∑ j, q i j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ i, w i := by simp_rw [hq, mul_one]
    _ = 1 := hw

/-- Weighted component entropy is at most the entropy of the mixture. -/
theorem weighted_entropy_le_mixture_entropy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (q : ι → κ → ℝ)
    (hw : (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1)
    (hq : ∀ i, (∀ j, 0 ≤ q i j) ∧ ∑ j, q i j = 1) :
    (∑ i, w i * shannonEntropy (q i)) ≤ shannonEntropy (mixture w q) := by
  have hjoint_nonneg := mixtureJoint_nonneg w q hw.1 fun i j => (hq i).1 j
  have hjoint_sum := mixtureJoint_sum_eq_one w q hw.2 fun i => (hq i).2
  have h := conditional_entropy_le_marginal (mixtureJoint w q)
    ⟨hjoint_nonneg, hjoint_sum⟩
  rw [mixtureJoint_conditionalEntropy_eq_weighted w q fun i => (hq i).2,
    mixtureJoint_swapped_marginal_eq_mixture w q] at h
  exact h

/-- Mixture entropy is at most weighted component entropy plus weight entropy. -/
theorem mixture_entropy_le_weighted_add_weight_entropy {ι κ : Type*}
    [Fintype ι] [Fintype κ] (w : ι → ℝ) (q : ι → κ → ℝ)
    (hw : (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1)
    (hq : ∀ i, (∀ j, 0 ≤ q i j) ∧ ∑ j, q i j = 1) :
    shannonEntropy (mixture w q) ≤
      shannonEntropy w + ∑ i, w i * shannonEntropy (q i) := by
  have hjoint_nonneg := mixtureJoint_nonneg w q hw.1 fun i j => (hq i).1 j
  have hswap_nonneg :
      ∀ z : κ × ι, 0 ≤ mixtureJoint w q (z.2, z.1) :=
    fun z => hjoint_nonneg (z.2, z.1)
  have hchain := entropy_chain_rule (mixtureJoint w q) hjoint_nonneg
  have hswap_chain := entropy_chain_rule
    (fun z : κ × ι => mixtureJoint w q (z.2, z.1)) hswap_nonneg
  have hswap_conditional := conditional_entropy_nonneg
    (fun z : κ × ι => mixtureJoint w q (z.2, z.1)) hswap_nonneg
  rw [mixtureJoint_marginal_eq_weight w q fun i => (hq i).2,
    mixtureJoint_conditionalEntropy_eq_weighted w q fun i => (hq i).2] at hchain
  rw [entropy_swap, mixtureJoint_swapped_marginal_eq_mixture w q] at hswap_chain
  linarith

/-- The mixture entropy gain over weighted component entropy is mutual information. -/
theorem mixture_entropy_sub_weighted_eq_mutual_information {ι κ : Type*}
    [Fintype ι] [Fintype κ] (w : ι → ℝ) (q : ι → κ → ℝ)
    (hw : (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1)
    (hq : ∀ i, (∀ j, 0 ≤ q i j) ∧ ∑ j, q i j = 1) :
    shannonEntropy (mixture w q) - ∑ i, w i * shannonEntropy (q i) =
      mutualInformation (mixtureJoint w q) := by
  have hjoint_nonneg := mixtureJoint_nonneg w q hw.1 fun i j => (hq i).1 j
  have hchain := entropy_chain_rule (mixtureJoint w q) hjoint_nonneg
  have hmi := mutual_information_eq_entropy_sub (mixtureJoint w q) hjoint_nonneg
  rw [mixtureJoint_marginal_eq_weight w q fun i => (hq i).2,
    mixtureJoint_conditionalEntropy_eq_weighted w q fun i => (hq i).2] at hchain
  rw [mixtureJoint_marginal_eq_weight w q fun i => (hq i).2,
    mixtureJoint_swapped_marginal_eq_mixture w q] at hmi
  linarith

/-- The lower mixture-entropy bound is sharp exactly for identical positive-weight components. -/
theorem mixture_entropy_eq_weighted_iff_components_eq {ι κ : Type*}
    [Fintype ι] [Fintype κ] (w : ι → ℝ) (q : ι → κ → ℝ)
    (hw : (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1)
    (hq : ∀ i, (∀ j, 0 ≤ q i j) ∧ ∑ j, q i j = 1) :
    shannonEntropy (mixture w q) = ∑ i, w i * shannonEntropy (q i) ↔
      ∀ i, w i ≠ 0 → q i = mixture w q := by
  have hjoint_nonneg := mixtureJoint_nonneg w q hw.1 fun i j => (hq i).1 j
  have hjoint_sum := mixtureJoint_sum_eq_one w q hw.2 fun i => (hq i).2
  have hjoint_law :
      (∀ z, 0 ≤ mixtureJoint w q z) ∧ ∑ z, mixtureJoint w q z = 1 :=
    ⟨hjoint_nonneg, hjoint_sum⟩
  constructor
  · intro heq
    have hdiff := mixture_entropy_sub_weighted_eq_mutual_information w q hw hq
    have hmi_zero : mutualInformation (mixtureJoint w q) = 0 := by
      linarith
    have hproduct :=
      (mutual_information_eq_zero_iff_product (mixtureJoint w q) hjoint_law).mp hmi_zero
    rw [mixtureJoint_marginal_eq_weight w q fun i => (hq i).2,
      mixtureJoint_swapped_marginal_eq_mixture w q] at hproduct
    intro i hwi
    funext j
    have hcell := congrFun hproduct (i, j)
    simp only [mixtureJoint] at hcell
    exact mul_left_cancel₀ hwi hcell
  · intro hcomponents
    have hproduct :
        mixtureJoint w q = fun z : ι × κ =>
          marginal (mixtureJoint w q) z.1 *
            marginal (fun r : κ × ι => mixtureJoint w q (r.2, r.1)) z.2 := by
      rw [mixtureJoint_marginal_eq_weight w q fun i => (hq i).2,
        mixtureJoint_swapped_marginal_eq_mixture w q]
      funext z
      simp only [mixtureJoint]
      by_cases hwi : w z.1 = 0
      · simp [hwi]
      · rw [hcomponents z.1 hwi]
    have hmi_zero : mutualInformation (mixtureJoint w q) = 0 :=
      (mutual_information_eq_zero_iff_product (mixtureJoint w q) hjoint_law).mpr hproduct
    have hdiff := mixture_entropy_sub_weighted_eq_mutual_information w q hw hq
    rw [hmi_zero] at hdiff
    exact sub_eq_zero.mp hdiff

end D5.S3.Entropy.Mixing.MixtureEntropyBracket

/- GID: D5/S3/Entropy/Submodularity/ConditionalMutualInformation
   generality: G
   mirror-B: D5/B/S3/Entropy/Submodularity/ConditionalMutualInformation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define conditional mutual information and identify its entropy defect. -/

import D5.S3.Entropy.Submodularity.StrongSubadditivity

namespace D5.S3.Entropy.Submodularity.ConditionalMutualInformation

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.Submodularity.StrongSubadditivity

/-- Conditional mutual information as the defect in conditional-entropy subadditivity. -/
noncomputable def conditionalMutualInformation {ι κ μ : Type*} [Fintype ι]
    [Fintype κ] [Fintype μ] (p : ι × (κ × μ) → ℝ) : ℝ :=
  conditionalEntropy (xyProjection p) + conditionalEntropy (xzProjection p) -
    conditionalEntropy p

/-- Conditional mutual information is nonnegative for every finite law. -/
theorem conditional_mutual_information_nonneg {ι κ μ : Type*} [Fintype ι]
    [Fintype κ] [Fintype μ] (p : ι × (κ × μ) → ℝ)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    0 ≤ conditionalMutualInformation p := by
  unfold conditionalMutualInformation
  linarith [conditionalEntropy_pair_le_add p hp]

/-- Conditional mutual information is the strong-subadditivity entropy defect. -/
theorem conditional_mutual_information_eq_entropy_defect
    {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (p : ι × (κ × μ) → ℝ) (hp : ∀ x, 0 ≤ p x) :
    conditionalMutualInformation p =
      shannonEntropy (xyProjection p) + shannonEntropy (xzProjection p) -
        shannonEntropy p - shannonEntropy (marginal p) := by
  classical
  have hxy_nonneg : ∀ q, 0 ≤ xyProjection p q := fun q =>
    Finset.sum_nonneg fun z _ => hp (q.1, (q.2, z))
  have hxz_nonneg : ∀ q, 0 ≤ xzProjection p q := fun q =>
    Finset.sum_nonneg fun y _ => hp (q.1, (y, q.2))
  have hxy_marginal : marginal (xyProjection p) = marginal p := by
    funext i
    simp only [marginal, xyProjection, Fintype.sum_prod_type]
  have hxz_marginal : marginal (xzProjection p) = marginal p := by
    funext i
    simp only [marginal, xzProjection, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  rw [entropy_chain_rule p hp, entropy_chain_rule (xyProjection p) hxy_nonneg,
    entropy_chain_rule (xzProjection p) hxz_nonneg, hxy_marginal, hxz_marginal]
  unfold conditionalMutualInformation
  ring

end D5.S3.Entropy.Submodularity.ConditionalMutualInformation

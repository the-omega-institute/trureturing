/- GID: D5/S3/Entropy/Observation/AuthorInformationDecomposition
   generality: G
   mirror-B: D5/B/S3/Entropy/Observation/AuthorInformationDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Action entropy splits into internal-state information and residual entropy. -/

import D5.S3.Entropy.Submodularity.ConditionalMutualInformation

/- Library-search audit trail (2026-08-27):
   * The canonical finite `conditionalEntropy`, `xyProjection`, `xzProjection`,
     and `conditionalMutualInformation` primitives are imported.
   * Repository searches found the entropy-defect definition and mutual-information
     chain rule, but no theorem stating this conditional action decomposition.
   * Pinned Mathlib has no matching finite real-valued conditional-entropy theorem. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Entropy.Observation.AuthorInformationDecomposition

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.Submodularity.ConditionalMutualInformation
open D5.S3.Entropy.Submodularity.StrongSubadditivity

/-- Conditional action entropy is the sum of the action information carried by
the internal state and the action entropy left after that state is known. -/
theorem author_information_decomposition
    {Public Action Memory : Type*}
    [Fintype Public] [Fintype Action] [Fintype Memory]
    (jointLaw : Public × (Action × Memory) -> ℝ)
    (hNonnegative : ∀ z, 0 ≤ jointLaw z) :
    let actionGivenPublicLaw := xyProjection jointLaw
    let actionGivenPublicMemoryLaw :=
      fun z : (Public × Memory) × Action =>
        jointLaw (z.1.1, (z.2, z.1.2))
    conditionalEntropy actionGivenPublicLaw =
      conditionalMutualInformation jointLaw +
        conditionalEntropy actionGivenPublicMemoryLaw := by
  let actionGivenPublicMemoryLaw :=
    fun z : (Public × Memory) × Action =>
      jointLaw (z.1.1, (z.2, z.1.2))
  change conditionalEntropy (xyProjection jointLaw) =
    conditionalMutualInformation jointLaw +
      conditionalEntropy actionGivenPublicMemoryLaw
  have hMemoryPublicNonnegative : ∀ z, 0 ≤ xzProjection jointLaw z := by
    intro z
    exact Finset.sum_nonneg fun action _ => hNonnegative (z.1, (action, z.2))
  have hActionPublicMemoryNonnegative :
      ∀ z, 0 ≤ actionGivenPublicMemoryLaw z := by
    intro z
    exact hNonnegative (z.1.1, (z.2, z.1.2))
  have hEntropyActionPublicMemory :
      shannonEntropy actionGivenPublicMemoryLaw = shannonEntropy jointLaw := by
    let reindex : ((Public × Memory) × Action) ≃
        Public × (Action × Memory) :=
      { toFun := fun z => (z.1.1, (z.2, z.1.2))
        invFun := fun z => ((z.1, z.2.2), z.2.1)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    dsimp only [actionGivenPublicMemoryLaw]
    exact Fintype.sum_equiv reindex _ _ (fun _ => rfl)
  have hMarginalActionPublicMemory :
      marginal actionGivenPublicMemoryLaw = xzProjection jointLaw := by
    funext z
    simp only [actionGivenPublicMemoryLaw, marginal, xzProjection]
  have hMarginalMemoryPublic :
      marginal (xzProjection jointLaw) = marginal jointLaw := by
    funext q
    simp only [marginal, xzProjection, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  have hJointChain := entropy_chain_rule jointLaw hNonnegative
  have hMemoryChain := entropy_chain_rule
    (xzProjection jointLaw) hMemoryPublicNonnegative
  have hActionPublicMemoryChain := entropy_chain_rule
    actionGivenPublicMemoryLaw hActionPublicMemoryNonnegative
  rw [hMarginalMemoryPublic] at hMemoryChain
  rw [hEntropyActionPublicMemory, hMarginalActionPublicMemory]
    at hActionPublicMemoryChain
  have hConditionalChain :
      conditionalEntropy jointLaw =
        conditionalEntropy (xzProjection jointLaw) +
          conditionalEntropy actionGivenPublicMemoryLaw := by
    linarith
  unfold conditionalMutualInformation
  linarith

#print axioms author_information_decomposition

end D5.S3.Entropy.Observation.AuthorInformationDecomposition

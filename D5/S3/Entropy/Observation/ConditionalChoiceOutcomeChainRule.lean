/- GID: D5/S3/Entropy/Observation/ConditionalChoiceOutcomeChainRule
   generality: G
   mirror-B: D5/B/S3/Entropy/Observation/ConditionalChoiceOutcomeChainRule
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Split choice-outcome uncertainty conditioned on a public context. -/

import D5.S3.Entropy.Submodularity.StrongSubadditivity

/- Library-search audit trail (2026-08-27):
   * Pinned Mathlib searches found no exact finite real-valued conditional-entropy
     chain rule on three finite carriers.
   * Current-tree searches found `entropy_chain_rule`, which handles one
     conditioning coordinate, and the canonical `xyProjection`; both are applied.
   * No new definition or abbreviation is introduced. The joint law, its public
     context-choice projection, and its reassociation as context-choice versus
     outcome are exposed directly in the statement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Entropy.Observation.ConditionalChoiceOutcomeChainRule

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.Submodularity.StrongSubadditivity

private theorem entropy_reassociate {Q A Y : Type*}
    [Fintype Q] [Fintype A] [Fintype Y]
    (p : Q × (A × Y) -> Real) :
    shannonEntropy p =
      shannonEntropy (fun z : (Q × A) × Y => p (z.1.1, (z.1.2, z.2))) := by
  simp only [shannonEntropy, Fintype.sum_prod_type]

/-- For a finite nonnegative joint law of public context, choice, and outcome,
the residual choice-outcome entropy given the context is the choice entropy
given the context plus the outcome entropy given both context and choice. -/
theorem conditional_choice_outcome_chain_rule
    {Q A Y : Type*} [Fintype Q] [Fintype A] [Fintype Y]
    (p : Q × (A × Y) -> Real) (nonnegative : forall z, 0 <= p z) :
    conditionalEntropy p =
      conditionalEntropy (xyProjection p) +
        conditionalEntropy
          (fun z : (Q × A) × Y => p (z.1.1, (z.1.2, z.2))) := by
  have projectedNonnegative : forall z, 0 <= xyProjection p z := by
    intro z
    exact Finset.sum_nonneg fun y _ => nonnegative (z.1, (z.2, y))
  have reassociatedNonnegative :
      forall z : (Q × A) × Y, 0 <= p (z.1.1, (z.1.2, z.2)) := by
    intro z
    exact nonnegative (z.1.1, (z.1.2, z.2))
  have marginalProjection : marginal (xyProjection p) = marginal p := by
    funext q
    simp only [marginal, xyProjection, Fintype.sum_prod_type]
  have reassociatedMarginal :
      marginal (fun z : (Q × A) × Y => p (z.1.1, (z.1.2, z.2))) =
        xyProjection p := by
    funext z
    rfl
  have whole := entropy_chain_rule p nonnegative
  have projected := entropy_chain_rule (xyProjection p) projectedNonnegative
  have reassociated := entropy_chain_rule
    (fun z : (Q × A) × Y => p (z.1.1, (z.1.2, z.2)))
    reassociatedNonnegative
  rw [marginalProjection] at projected
  rw [reassociatedMarginal, projected] at reassociated
  rw [<- entropy_reassociate p] at reassociated
  linarith

#print axioms conditional_choice_outcome_chain_rule

end D5.S3.Entropy.Observation.ConditionalChoiceOutcomeChainRule

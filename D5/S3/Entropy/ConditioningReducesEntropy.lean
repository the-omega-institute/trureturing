/- GID: D5/S3/Entropy/ConditioningReducesEntropy
   generality: G
   mirror-B: D5/B/S3/Entropy/ConditioningReducesEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove conditioning cannot increase finite Shannon entropy. -/

/- Library-search audit trail (2026-08-09):
   * Local pinned-mathlib grep terms: `conditionalEntropy`, `conditional_entropy`,
     `condEntropy`, `conditioning.*entropy`, `entropy.*conditioning`,
     `condition.*reduce.*entropy`, `shannonEntropy`, `finiteEntropy`,
     `entropy_subadditive`, and mutual-information name variants.
   * Pinned mathlib provides measure-valued KL chain rules and the scalar Shannon atom
     `Real.negMulLog`, but no finite conditional-entropy definition or conditioning bound.
   * Repository-wide `D5/` grep covered conditional-entropy names and orderings,
     `shannonEntropy` adjacent to `marginal`, inequalities in both orientations,
     `sub_nonneg` forms, curried variants, and rearrangements involving mutual information.
     No duplicate was found; the proof below composes the repository's frozen entropy chain
     rule, mutual-information entropy decomposition, and mutual-information nonnegativity.
   * Units are nats because `shannonEntropy` uses the natural logarithm through
     `Real.negMulLog`.
-/

import D5.S3.Entropy.ConditionalEntropy
import D5.S3.Entropy.MutualInformationEntropy

namespace D5.S3.Entropy.ConditioningReducesEntropy

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationEntropy

/-- Conditioning on the first coordinate cannot increase the entropy of the second. -/
theorem conditional_entropy_le_marginal {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    conditionalEntropy p ≤
      shannonEntropy (marginal (fun r : κ × ι => p (r.2, r.1))) := by
  have hmi := mutual_information_nonneg p hp
  rw [mutual_information_eq_entropy_sub p hp.1, entropy_chain_rule p hp.1] at hmi
  linarith

end D5.S3.Entropy.ConditioningReducesEntropy

/- GID: D5/S3/Entropy/Submodularity/PredictionClosureCriterion
   generality: G
   mirror-B: D5/B/S3/Entropy/Submodularity/PredictionClosureCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize predictive closure by conditional factorization. -/

import D5.S3.Entropy.Submodularity.MarkovDataProcessing

/- Library-search audit trail (2026-08-25):
   * Exact current-tree hit
     `MarkovDataProcessing.conditional_mutual_information_eq_zero_iff_conditional_product`
     characterizes zero conditional mutual information by product factorization on every
     active conditioning slice. It is applied directly below.
   * `MutualInformationChainRule` applies the same frozen result to related equality cases.
   * Pinned Mathlib has measure-theoretic conditional-independence interfaces, but the search
     found no packaged theorem on this repository's finite real-valued mass-function carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Entropy.Submodularity.PredictionClosureCriterion

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.Submodularity.ConditionalMutualInformation
open D5.S3.Entropy.Submodularity.MarkovDataProcessing

/-- For a deterministic finite current interface, its conditional mutual information between
the complete past and future vanishes exactly when their conditional law factors on every
current-interface value of nonzero mass. -/
theorem prediction_closure_iff_markov
    {Past Current Future : Type*}
    [Fintype Past] [Fintype Current] [Fintype Future]
    (q : Past → Current) (p : Current × (Past × Future) → ℝ)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1)
    (_hInterface : ∀ c past future, p (c, (past, future)) ≠ 0 → c = q past) :
    conditionalMutualInformation p = 0 ↔
      ∀ c, marginal p c ≠ 0 →
        conditional p c = fun x : Past × Future =>
          marginal (conditional p c) x.1 *
            marginal (fun y : Future × Past => conditional p c (y.2, y.1)) x.2 := by
  exact conditional_mutual_information_eq_zero_iff_conditional_product p hp

example :
    ∃ (q : Unit → Unit) (p : Unit × (Unit × Unit) → ℝ),
      ((∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) ∧
        (∀ c past future, p (c, (past, future)) ≠ 0 → c = q past) := by
  refine ⟨id, fun _ => 1, ?_, ?_⟩
  · simp
  · simp

#print axioms prediction_closure_iff_markov

end D5.S3.Entropy.Submodularity.PredictionClosureCriterion

/- GID: D5/S3/Estimation/DecisionRisk/PosteriorFuturePolicySufficiency
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/PosteriorFuturePolicySufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal posteriors give equal Bayes values for every future policy and loss. -/

import D5.S3.Estimation.DecisionRisk.PosteriorUniversalSufficiency
import Mathlib.Probability.ProbabilityMassFunction.Basic

/- Library-search audit trail (2026-08-25):
   * The exact family theorem `posterior_universal_sufficiency` covers the
     current one-step stopping value, but its frozen digest explicitly excludes
     arbitrary-horizon experiment policies. It is imported for the canonical
     `posterior` primitive rather than wrapped as an exact hit.
   * Repository body-shape searches for policy-indexed PMFs, posterior-weighted
     future transcript laws, and an infimum over transcript decision rules found
     no existing declaration. This module introduces no `def` or `abbrev`.
   * Pinned Mathlib's `PMF` is the canonical normalized discrete law on an
     arbitrary future-transcript carrier. Complete-lattice infima and countable
     sums provide the conditional Bayes value; no exact whole-theorem hit exists. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ENNReal NNReal

noncomputable section

namespace D5.S3.Estimation.DecisionRisk.PosteriorFuturePolicySufficiency

open D5.S3.Estimation.DecisionRisk.PosteriorUniversalSufficiency

universe u

/-- A future experiment policy is represented by its state-conditioned PMF on
the complete future transcript. For every such policy, arbitrary action space,
and arbitrary nonnegative loss, equal history posteriors give equal conditional
Bayes values. The displayed infimum ranges over every terminal decision rule on
the future transcript, so the policy clause is public rather than hidden in a
helper theorem. -/
theorem posterior_future_policy_universal_sufficiency
    {Theta History Policy Future : Type*} [Fintype Theta]
    (joint : Theta → History → NNReal)
    (futureExperimentLaw : Policy → Theta → PMF Future)
    {history history' : History}
    (equalPosterior : posterior joint history = posterior joint history') :
    ∀ (policy : Policy) (Action : Type u) (loss : Theta → Action → ENNReal),
      (⨅ decision : Future → Action,
        ∑ theta,
          (posterior joint history theta : ENNReal) *
            ∑' future,
              futureExperimentLaw policy theta future *
                loss theta (decision future)) =
      ⨅ decision : Future → Action,
        ∑ theta,
          (posterior joint history' theta : ENNReal) *
            ∑' future,
              futureExperimentLaw policy theta future *
                loss theta (decision future) := by
  intro policy Action loss
  rw [equalPosterior]

#print axioms posterior_future_policy_universal_sufficiency

end D5.S3.Estimation.DecisionRisk.PosteriorFuturePolicySufficiency

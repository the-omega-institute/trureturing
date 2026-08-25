/- GID: D5/S3/Estimation/DecisionRisk/CausalPosteriorSufficiency
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/CausalPosteriorSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite causal posterior determines future predictions and Bayes decisions. -/

import D5.S3.Estimation.DecisionRisk.PosteriorFuturePolicySufficiency

/- Library-search audit trail (2026-08-26):
   * Exact family primitives `posterior` and `PMF` encode the finite causal
     belief and every model/intervention-conditioned future output law.
   * `posterior_future_policy_universal_sufficiency` supplies only an infimum
     value; it omits public predictive masses and the complete optimizer set.
   * `experiment_state_and_posterior_decision_separation` supplies finite
     optimizer sets but no future intervention law or prediction clause.
     Neither existing theorem is an exact bind for this atom.
   * Body-shape searches for the posterior mixture and output-dependent
     optimizer set found no existing D5 definition. They are stated directly
     below; no new `def` or `abbrev` is introduced.
   * Pinned Mathlib's finite sums, `tsum`, and `PMF` evaluation are applied
     directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ENNReal NNReal

noncomputable section

namespace D5.S3.Estimation.DecisionRisk.CausalPosteriorSufficiency

open D5.S3.Estimation.DecisionRisk.PosteriorUniversalSufficiency

universe u

/-- If a complete future output law depends only on the true finite model and
the selected intervention, equal causal posteriors determine every future
predictive mass and, for every loss, the complete set of Bayes-optimal decision
rules on the future output. -/
theorem causal_posterior_determines_predictions_and_bayes_decisions
    {Model History Intervention Future : Type*} [Fintype Model]
    (joint : Model → History → NNReal)
    (futureLaw : Intervention → Model → PMF Future)
    {history history' : History}
    (equalPosterior : posterior joint history = posterior joint history') :
    (∀ intervention future,
      (∑ model,
          (posterior joint history model : ENNReal) *
            futureLaw intervention model future) =
        ∑ model,
          (posterior joint history' model : ENNReal) *
            futureLaw intervention model future) ∧
      ∀ (intervention : Intervention) (Action : Type u)
          (loss : Model → Action → ENNReal),
        {decision : Future → Action | ∀ alternative : Future → Action,
          (∑ model,
              (posterior joint history model : ENNReal) *
                ∑' future,
                  futureLaw intervention model future *
                    loss model (decision future)) ≤
            ∑ model,
              (posterior joint history model : ENNReal) *
                ∑' future,
                  futureLaw intervention model future *
                    loss model (alternative future)} =
          {decision : Future → Action | ∀ alternative : Future → Action,
            (∑ model,
                (posterior joint history' model : ENNReal) *
                  ∑' future,
                    futureLaw intervention model future *
                      loss model (decision future)) ≤
              ∑ model,
                (posterior joint history' model : ENNReal) *
                  ∑' future,
                    futureLaw intervention model future *
                      loss model (alternative future)} := by
  constructor
  · intro intervention future
    rw [equalPosterior]
  · intro intervention Action loss
    rw [equalPosterior]

#print axioms causal_posterior_determines_predictions_and_bayes_decisions

end D5.S3.Estimation.DecisionRisk.CausalPosteriorSufficiency

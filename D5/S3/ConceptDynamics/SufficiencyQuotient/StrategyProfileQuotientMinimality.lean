/- GID: D5/S3/ConceptDynamics/SufficiencyQuotient/StrategyProfileQuotientMinimality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SufficiencyQuotient/StrategyProfileQuotientMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strategy-sufficient history interfaces uniquely cover their profile quotient. -/

import D5.S3.ConceptDynamics.SufficiencyQuotient.MinimalPredictionBeliefState
import Mathlib.Probability.ProbabilityMassFunction.Basic

/- Library-search audit trail (2026-08-27):
   * Exact repository primitive `jointReadout` is the canonical indexed profile
     constructor; the supplied strategy profile is proved equal to its future-word
     instance rather than redeclared under a sibling name.
   * The closest frozen theorem `minimal_prediction_belief_state` constructs the
     unique map from a sufficient summary image to a joint-readout kernel quotient.
     It is applied directly, with the source's strategy profile exposed as the
     quotient kernel rather than replaced by its realized image.
   * `causal_state_factorization` ends at the realized profile image, while
     `realized_image_unique_factorization_iff_reverse_kernel` ends at another
     realized image; neither states the source's canonical history quotient.
   * Exact pinned-Mathlib hits `PMF`, `Setoid.ker`, `Set.rangeFactorization`, and
     `Set.rangeFactorization_surjective` supply the probability carrier, quotient
     relation, effective summary image, and uniqueness. No whole-theorem hit was found.
   * Body-shape searches for strategy-profile kernel quotients and unique maps from
     realized summary ranges found no other D5 declaration. No new `def` or `abbrev`
     is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.SufficiencyQuotient.StrategyProfileQuotientMinimality

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.SufficiencyQuotient.MinimalPredictionBeliefState

universe uHistory uFutureWord uAction uSummary

/-- If a realized history interface determines the complete future-word-indexed
strategy profile, it admits a unique map onto the quotient of histories by
equality of that profile. -/
theorem strategy_sufficient_self_universal_minimality
    {History : Type uHistory} {FutureWord : Type uFutureWord}
    {Action : Type uAction} {Summary : Type uSummary}
    (strategyProfile : History -> FutureWord -> PMF Action)
    (summary : History -> Summary)
    (predictor : Summary -> FutureWord -> PMF Action)
    (sufficient : strategyProfile = predictor ∘ summary) :
    ∃! factor : Set.range summary -> Quotient (Setoid.ker strategyProfile),
      ∀ history,
        Quotient.mk (Setoid.ker strategyProfile) history =
          factor (Set.rangeFactorization summary history) := by
  have profileIdentity :
      jointReadout (fun future : FutureWord => fun history : History =>
        strategyProfile history future) = strategyProfile := by
    funext history future
    rfl
  have sufficientJoint :
      jointReadout (fun future : FutureWord => fun history : History =>
        strategyProfile history future) = predictor ∘ summary := by
    exact profileIdentity.trans sufficient
  have factorResult :
      ∃! factor : Set.range summary -> Quotient (Setoid.ker strategyProfile),
        (fun history => Quotient.mk (Setoid.ker strategyProfile) history) =
            factor ∘ Set.rangeFactorization summary ∧
          Function.Surjective factor := by
    rw [← profileIdentity]
    exact (minimal_prediction_belief_state.{
      uHistory, uFutureWord, uSummary, uAction, 0}
        (possibleObservation := fun future : FutureWord => fun history : History =>
          strategyProfile history future)
        summary predictor sufficientJoint).2
  rcases factorResult with ⟨factor, ⟨factorization, _surjective⟩, _unique⟩
  have factorAt : ∀ history,
      Quotient.mk (Setoid.ker strategyProfile) history =
        factor (Set.rangeFactorization summary history) := by
    intro history
    have equation := congrFun factorization history
    simpa only [Function.comp_apply] using equation
  refine ⟨factor, factorAt, ?_⟩
  intro other otherAt
  apply Set.rangeFactorization_surjective.injective_comp_right
  funext history
  change other (Set.rangeFactorization summary history) =
    factor (Set.rangeFactorization summary history)
  exact (otherAt history).symm.trans (factorAt history)

#print axioms strategy_sufficient_self_universal_minimality

end D5.S3.ConceptDynamics.SufficiencyQuotient.StrategyProfileQuotientMinimality

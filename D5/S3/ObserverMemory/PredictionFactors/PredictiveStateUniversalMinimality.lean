/- GID: D5/S3/ObserverMemory/PredictionFactors/PredictiveStateUniversalMinimality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionFactors/PredictiveStateUniversalMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every sufficient past statistic uniquely maps its realized image to the canonical predictive state. -/

import D5.S3.ObserverMemory.PredictionFactors.CausalStateFactorization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.PredictionFactors.PredictiveStateUniversalMinimality

open D5.S3.ObserverMemory.PredictionFactors.CausalStateFactorization

theorem predictive_state_universal_minimality
    {Past Interface FutureLaw : Type*}
    (futureLaw : Past → FutureLaw) (statistic : Past → Interface)
    (predictor : Interface → FutureLaw)
    (sufficient : futureLaw = predictor ∘ statistic) :
    ExistsUnique fun factor : Set.range statistic → Set.range futureLaw =>
      Set.rangeFactorization futureLaw =
        factor ∘ Set.rangeFactorization statistic := by
  rcases (causal_state_factorization statistic futureLaw predictor sufficient).1 with
    ⟨factor, factor_properties, _⟩
  refine ⟨factor, factor_properties.1, ?_⟩
  intro other other_factorization
  apply Set.rangeFactorization_surjective.injective_comp_right
  exact other_factorization.symm.trans factor_properties.1

#print axioms predictive_state_universal_minimality

end D5.S3.ObserverMemory.PredictionFactors.PredictiveStateUniversalMinimality

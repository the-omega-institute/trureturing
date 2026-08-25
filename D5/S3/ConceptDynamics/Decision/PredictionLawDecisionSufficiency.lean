/- GID: D5/S3/ConceptDynamics/Decision/PredictionLawDecisionSufficiency
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Decision/PredictionLawDecisionSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A predictive-law factor determines expected losses and their minimizing actions. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/- Library-search audit trail (2026-08-25):
   * Exact family hits `Concept` and `Refines` supply the canonical readout and
     factor-map relation used directly below.
   * Body-shape searches for PMF expected-loss profiles and optimizer sets found
     only an older sibling theorem with an unnecessary integrability premise
     and finite specializations, not this unrestricted statement.
   * Pinned Mathlib supplies the total PMF-to-measure integral construction but
     no exact prediction-to-decision factorization theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Decision.PredictionLawDecisionSufficiency

open MeasureTheory
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- A concept that determines the predictive PMF also determines the complete
expected-loss profile and the set of actions minimizing that same profile. -/
theorem prediction_law_sufficiency_implies_decision_sufficiency
    {X C Outcome Action : Type*}
    [MeasurableSpace Outcome] [MeasurableSingletonClass Outcome]
    (prediction : Concept X (PMF Outcome))
    (concept : Concept X C)
    (loss : Action -> Outcome -> Real) :
    Refines prediction concept ->
      Refines
          (fun x action => integral (prediction x).toMeasure (loss action))
          concept ∧
        Refines
          (fun x => {action | forall alternative,
            integral (prediction x).toMeasure (loss action) <=
              integral (prediction x).toMeasure (loss alternative)})
          concept := by
  rintro ⟨factor, predictionFactors⟩
  constructor
  · refine ⟨fun c action => integral (factor c).toMeasure (loss action), ?_⟩
    funext x action
    rw [predictionFactors]
    rfl
  · refine ⟨fun c => {action | forall alternative,
      integral (factor c).toMeasure (loss action) <=
        integral (factor c).toMeasure (loss alternative)}, ?_⟩
    funext x
    ext action
    simp only [Set.mem_setOf_eq]
    rw [predictionFactors]
    rfl

#print axioms prediction_law_sufficiency_implies_decision_sufficiency

end D5.S3.ConceptDynamics.Decision.PredictionLawDecisionSufficiency

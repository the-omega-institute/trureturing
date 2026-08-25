/- GID: D5/S3/ConceptDynamics/Decision/PredictionDecisionSufficiency
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Decision/PredictionDecisionSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A sufficient predictive readout determines expected losses and optimal actions. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/- Library-search audit trail (2026-08-25):
   * Exact family hits `Concept` and `Refines` supply the canonical readout and
     factor-map refinement relation used directly below.
   * Searches for PMF expected-loss profiles, decision sufficiency, and
     optimizer-set descent found only finite posterior and finite-horizon
     specializations, not this general prediction-to-decision theorem.
   * Pinned Mathlib supplies the canonical `PMF.toMeasure` expectation
     semantics, but no theorem packages the two refinement conclusions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Decision.PredictionDecisionSufficiency

open MeasureTheory
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- If a concept determines the complete predictive law, then it determines
the expected loss of every action and the set of actions minimizing that same
expected-loss profile. -/
theorem prediction_sufficiency_implies_decision_sufficiency
    {X C Outcome Action : Type*}
    [MeasurableSpace Outcome] [MeasurableSingletonClass Outcome]
    (prediction : Concept X (PMF Outcome))
    (concept : Concept X C)
    (loss : Action -> Outcome -> Real)
    (_lossIntegrable : forall x action,
      Integrable (loss action) (prediction x).toMeasure) :
    let expectedLoss : Concept X (Action -> Real) :=
      fun x action => integral (prediction x).toMeasure (loss action)
    let optimalActions : Concept X (Set Action) :=
      fun x => {action | forall alternative,
        expectedLoss x action <= expectedLoss x alternative}
    Refines prediction concept ->
      Refines expectedLoss concept /\ Refines optimalActions concept := by
  dsimp only
  intro predictionRefines
  rcases predictionRefines with ⟨factor, predictionFactors⟩
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

#print axioms prediction_sufficiency_implies_decision_sufficiency

end D5.S3.ConceptDynamics.Decision.PredictionDecisionSufficiency

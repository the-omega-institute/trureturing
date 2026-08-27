/- GID: D5/S3/ConceptDynamics/Decision/PredictionDecisionSufficiencyStrictness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Decision/PredictionDecisionSufficiencyStrictness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prediction determines losses and actions, but actions need not determine prediction. -/

import D5.S3.ConceptDynamics.Decision.PredictionLawDecisionSufficiency
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-27):
   * The exact frozen forward owner is
     `PredictionLawDecisionSufficiency.prediction_law_sufficiency_implies_decision_sufficiency`;
     it is imported and applied rather than wrapped or reproved in isolation.
   * Repository searches for PMF-valued decision sufficiency, full-prediction strictness,
     equal optimal actions under distinct predictive laws, and negated prediction refinement
     found no theorem packaging both the forward implication and its converse countermodel.
   * `DecisionWithoutFullPrediction` has an adjacent payoff-profile countermodel, but its
     negative object is not a predictive distribution and therefore is not an exact carrier hit.
   * Pinned Mathlib supplies `PMF.pure`, its evaluation lemmas, and Dirac integration; it has no
     theorem packaging the source's refinement comparison. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Decision.PredictionDecisionSufficiencyStrictness

open MeasureTheory
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Decision.PredictionLawDecisionSufficiency

/-- Predictive-law sufficiency determines both the expected-loss profile and its optimizer set.
The converse to optimizer-set sufficiency fails on two distinct deterministic predictive laws:
an outcome-dependent loss has the same unique optimal action in both states, so a constant concept
determines the optimizer set without determining the predictive law. -/
theorem prediction_sufficiency_implies_decision_sufficiency_strictly
    {X C Outcome Action : Type*}
    [MeasurableSpace Outcome] [MeasurableSingletonClass Outcome]
    (prediction : Concept X (PMF Outcome))
    (concept : Concept X C)
    (loss : Action -> Outcome -> Real) :
    (Refines prediction concept ->
      Refines
          (fun x action => integral (prediction x).toMeasure (loss action))
          concept /\
        Refines
          (fun x => {action | forall alternative,
            integral (prediction x).toMeasure (loss action) <=
              integral (prediction x).toMeasure (loss alternative)})
          concept) /\
      (let predictionExample : Concept Bool (PMF Bool) :=
          fun state => PMF.pure state
       let lossExample : Bool -> Bool -> Real :=
          fun action outcome => if action then 0 else if outcome then 2 else 1
       let expectedLossExample : Concept Bool (Bool -> Real) :=
          fun state action =>
            integral (predictionExample state).toMeasure (lossExample action)
       let optimalActionsExample : Concept Bool (Set Bool) :=
          fun state => {action | forall alternative,
            expectedLossExample state action <= expectedLossExample state alternative}
       let conceptExample : Concept Bool Unit := fun _ => ()
       Refines optimalActionsExample conceptExample /\
         Not (Refines predictionExample conceptExample)) := by
  constructor
  · exact prediction_law_sufficiency_implies_decision_sufficiency
      prediction concept loss
  · dsimp only
    constructor
    · refine ⟨fun _ => ({true} : Set Bool), ?_⟩
      funext state
      ext action
      cases state <;> cases action <;> simp [PMF.toMeasure_pure]
    · rintro ⟨factor, predictionFactors⟩
      have equalPredictions : PMF.pure false = PMF.pure true := by
        calc
          PMF.pure false = factor () := by
            simpa using congrFun predictionFactors false
          _ = PMF.pure true := by
            simpa using (congrFun predictionFactors true).symm
      have falseMass := congrArg (fun pmf : PMF Bool => pmf false) equalPredictions
      norm_num [PMF.pure_apply] at falseMass

#print axioms prediction_sufficiency_implies_decision_sufficiency_strictly

end D5.S3.ConceptDynamics.Decision.PredictionDecisionSufficiencyStrictness

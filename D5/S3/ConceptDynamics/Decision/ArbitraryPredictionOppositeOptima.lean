/- GID: D5/S3/ConceptDynamics/Decision/ArbitraryPredictionOppositeOptima
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Decision/ArbitraryPredictionOppositeOptima
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every PMF prediction admits opposite unique optima under two constant loss models. -/

import D5.S3.ConceptDynamics.Decision.PredictionLawDecisionSufficiency

/- Library-search audit trail (2026-08-27):
   * The imported decision-family owner supplies the canonical PMF integral and
     full optimizer-set shapes; both are used inline rather than redeclared.
   * The frozen `SamePredictionOppositeOptima` theorem constructs only a
     `Bool -> PMF Unit` example, so it is not the arbitrary-law statement here.
   * Pinned Mathlib supplies constant integration against a probability measure,
     but no theorem packages both opposite singleton optimizer clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Decision.ArbitraryPredictionOppositeOptima

open MeasureTheory

/-- For any one predictive PMF law, the two constant Boolean-action losses
select opposite unique actions at every state. -/
theorem arbitrary_prediction_opposite_unique_optima
    {X Outcome : Type*}
    [MeasurableSpace Outcome] [MeasurableSingletonClass Outcome]
    (prediction : X -> PMF Outcome) :
    let lossFalse : Bool -> Outcome -> Real :=
      fun action _ => if action then 1 else 0
    let lossTrue : Bool -> Outcome -> Real :=
      fun action _ => if action then 0 else 1
    let expectedLoss :
        (Bool -> Outcome -> Real) -> X -> Bool -> Real :=
      fun loss state action =>
        integral (prediction state).toMeasure (loss action)
    let optimalActions :
        (Bool -> Outcome -> Real) -> X -> Set Bool :=
      fun loss state => {action | forall alternative,
        expectedLoss loss state action <=
          expectedLoss loss state alternative}
    (forall state, optimalActions lossFalse state = {false}) /\
      forall state, optimalActions lossTrue state = {true} := by
  dsimp only
  constructor
  · intro state
    ext action
    cases action <;> simp [integral_const]
  · intro state
    ext action
    cases action <;> simp [integral_const]

#print axioms arbitrary_prediction_opposite_unique_optima

end D5.S3.ConceptDynamics.Decision.ArbitraryPredictionOppositeOptima

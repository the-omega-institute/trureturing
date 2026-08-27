/- GID: D5/S3/ConceptDynamics/Decision/SamePredictionOppositeOptima
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Decision/SamePredictionOppositeOptima
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One PMF prediction has opposite unique optima under two loss models. -/

import D5.S3.ConceptDynamics.Decision.PredictionDecisionSufficiency

/- Library-search audit trail (2026-08-27):
   * The imported decision-family owner supplies the canonical PMF expectation
     and full optimizer-set shapes; they are used inline rather than forked.
   * Adjacent frozen modules exhibit either nonunique optima or distinct
     predictions with a common optimum, but no theorem has one prediction and
     two losses with opposite unique optimal actions.
   * Pinned Mathlib supplies `PMF.pure`, Dirac integration, and Boolean case
     simplification, but no packaged decision-value countermodel. -/

namespace D5.S3.ConceptDynamics.Decision.SamePredictionOppositeOptima

open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A single PMF-valued prediction interface does not determine value: two
loss models give opposite singleton optimizer sets on every state. -/
theorem same_prediction_opposite_unique_optima :
    ∃ (prediction : Bool -> PMF Unit)
      (lossFalse lossTrue : Bool -> Unit -> Real),
      let expectedLoss :
          (Bool -> Unit -> Real) -> Bool -> Bool -> Real :=
        fun loss state action =>
          integral (prediction state).toMeasure (loss action)
      let optimalActions :
          (Bool -> Unit -> Real) -> Bool -> Set Bool :=
        fun loss state => {action | ∀ alternative,
          expectedLoss loss state action <=
            expectedLoss loss state alternative}
      (∀ state, optimalActions lossFalse state = {false}) ∧
        ∀ state, optimalActions lossTrue state = {true} := by
  refine ⟨fun _ => PMF.pure (),
    fun action _ => if action then 1 else 0,
    fun action _ => if action then 0 else 1, ?_⟩
  dsimp only
  constructor
  · intro state
    ext action
    cases action <;> simp [PMF.toMeasure_pure]
  · intro state
    ext action
    cases action <;> simp [PMF.toMeasure_pure]

#print axioms same_prediction_opposite_unique_optima

end D5.S3.ConceptDynamics.Decision.SamePredictionOppositeOptima

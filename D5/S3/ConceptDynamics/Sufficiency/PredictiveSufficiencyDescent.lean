/- GID: D5/S3/ConceptDynamics/Sufficiency/PredictiveSufficiencyDescent
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Sufficiency/PredictiveSufficiencyDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Predictive completion carries the update and the current readout. -/

import D5.S3.ObserverMemory.Refinement.PredictionCompletion

/- Library-search audit trail (2026-08-25):
   * Exact family hits `CompletedState`, `completionProjection`,
     `completionUpdate`, and `completionReadout` are imported and exposed
     directly; no quotient or descent object is redeclared.
   * `minimal_predictive_completion_quotient` additionally states a coarsest
     property through a sibling quotient presentation, so it is not an exact
     bind-only theorem for the named two-clause result.
   * `behavior_completion_characterization` uses these two equations only as
     private local facts inside a stronger characterization theorem.
   * Pinned Mathlib's `Quotient.map` and `Quotient.lift` already construct the
     imported canonical maps; no library theorem packages both computations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Sufficiency.PredictiveSufficiencyDescent

open D5.S3.ObserverMemory.Refinement.PredictionCompletion

/-- On the quotient by equality of complete future readouts, the canonical
update sends the class of a state to the class of its update, and the canonical
readout recovers the current readout on every representative. -/
theorem predictive_sufficiency_descent
    {X O : Type*} (update : X -> X) (readout : X -> O) :
    (forall state,
      completionUpdate update readout
          (completionProjection update readout state) =
        completionProjection update readout (update state)) ∧
    (forall state,
      completionReadout update readout
          (completionProjection update readout state) =
        readout state) := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩

#print axioms predictive_sufficiency_descent

end D5.S3.ConceptDynamics.Sufficiency.PredictiveSufficiencyDescent

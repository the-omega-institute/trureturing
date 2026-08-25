/- GID: D5/S3/ObserverMemory/Dynamics/ControlledInterventionDescentUniqueness
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Dynamics/ControlledInterventionDescentUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every controlled update descends uniquely through behavior completion. -/

import D5.S0.Rewriting.Quotients.DynamicsDescent
import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Dynamics.ControlledInterventionDescentUniqueness

open D5.S0.Rewriting.Quotients.DynamicsDescent
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/-- Every controlled update has a unique endomap on the canonical behavior
completion that makes the projection square commute. -/
theorem all_interventions_unique_completion_descent
    {U Y O : Type*} (update : U -> Y -> Y) (readout : Y -> O) :
    forall u : U,
      ExistsUnique fun descended :
          ControlledCompletion update readout ->
            ControlledCompletion update readout =>
        completionProjection update readout ∘ update u =
          descended ∘ completionProjection update readout := by
  intro u
  apply (dynamics_descends_iff
    (completionProjection update readout) (update u)
    Quotient.mk_surjective).2
  intro y y' hyy'
  calc
    completionProjection update readout (update u y) =
        completionUpdate update readout u
          (completionProjection update readout y) := rfl
    _ = completionUpdate update readout u
          (completionProjection update readout y') := congrArg _ hyy'
    _ = completionProjection update readout (update u y') := rfl

#print axioms all_interventions_unique_completion_descent

end D5.S3.ObserverMemory.Dynamics.ControlledInterventionDescentUniqueness

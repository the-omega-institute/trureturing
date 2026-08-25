/- GID: D5/S3/ObserverMemory/Dynamics/InterventionCompletionNaturality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Dynamics/InterventionCompletionNaturality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every controlled intervention commutes with the canonical completion projection on diagonals. -/

import D5.S3.Observer.Naturality.DiagonalNaturalityDefect
import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Dynamics.InterventionCompletionNaturality

open D5.S3.Observer.Naturality.DiagonalNaturalityDefect
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/- The completion projection and induced update are the canonical quotient objects. -/
theorem all_interventions_completion_naturality
    {A U Y O : Type*}
    (update : U -> Y -> Y) (readout : Y -> O)
    (table : A × A -> Y) :
    forall u : U,
      pointwiseOutputProjection (completionProjection update readout)
          (diagonalUpdate (update u) table) =
        diagonalUpdate (completionUpdate update readout u)
          (pointwiseTableProjection (completionProjection update readout) table) := by
  intro u
  funext address
  rfl

#print axioms all_interventions_completion_naturality

end D5.S3.ObserverMemory.Dynamics.InterventionCompletionNaturality

/- GID: D5/S3/ObserverMemory/Refinement/CanonicalCompletionIdempotence
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Refinement/CanonicalCompletionIdempotence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical second predictive completion is equivalent to the first. -/

import D5.S3.ObserverMemory.Refinement.CascadeCompletion

/- Library-search audit trail (2026-08-25):
   * The exact repository hit `cascadeCompletionEquiv` is the canonical
     equivalence between the second-stage quotient and direct completion; it is
     applied directly below with the identity forgetting map.
   * No additional repository or pinned Mathlib theorem was needed because the
     imported declaration already exposes the required canonical object.
-/

namespace D5.S3.ObserverMemory.Refinement.CanonicalCompletionIdempotence

open D5.S3.ObserverMemory.Refinement.PredictionCompletion
open D5.S3.ObserverMemory.Refinement.CascadeCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Applying predictive completion twice gives the canonical first completion. -/
def canonical_completion_idempotence {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) :
    Quotient (secondStageRelation update readout (id : O -> O)) ≃
      CompletedState update readout := by
  exact cascadeCompletionEquiv update readout readout (id : O -> O) rfl

#print axioms canonical_completion_idempotence

end D5.S3.ObserverMemory.Refinement.CanonicalCompletionIdempotence

/- GID: D5/S3/ObserverMemory/Trajectories/BehaviorCompletionExtensivity
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/BehaviorCompletionExtensivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Behavior completion uniquely refines the current readout. -/

import D5.S3.ObserverMemory.Trajectories.CompletionExtensivity

/- Library-search audit trail (2026-08-25):
   * Exact family hit `completion_extensivity` states unique factorization of
     the current readout through the realized complete itinerary; it is
     imported and applied directly.
   * Exact supporting family hits `completeItinerary` and `ItineraryRange`
     construct the source behavior completion from future readout semantics.
   * Exact pinned-Mathlib hit `Set.rangeFactorization` supplies the canonical
     map from a state into the effective completion image. -/

namespace D5.S3.ObserverMemory.Trajectories.BehaviorCompletionExtensivity

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.Trajectories.CompletionExtensivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The current readout factors uniquely through its realized behavior
completion, so the complete future itinerary refines the original readout. -/
theorem behavior_completion_extensivity {X B : Type*}
    (F : X -> X) (q : X -> B) :
    ∃! factor : ItineraryRange F q -> B,
      q = factor ∘ Set.rangeFactorization (completeItinerary F q) := by
  exact completion_extensivity F q

#print axioms behavior_completion_extensivity

end D5.S3.ObserverMemory.Trajectories.BehaviorCompletionExtensivity

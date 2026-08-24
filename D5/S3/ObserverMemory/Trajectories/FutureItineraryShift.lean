/- GID: D5/S3/ObserverMemory/Trajectories/FutureItineraryShift
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/FutureItineraryShift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Updating a state shifts its complete future itinerary by one coordinate. -/

import D5.S3.ObserverMemory.Prediction.ItineraryCompletion
import Mathlib.Data.Stream.Init

/- Library-search audit trail (2026-08-25):
   * Exact repository hit `completeItinerary` is the canonical family trace and is
     imported and exposed directly in the statement.
   * Exact pinned-Mathlib hits `Stream'.tail` and `Function.iterate_succ_apply`
     are exposed and applied directly. `Stream'.tail_iterate` is structurally
     related but does not state the equality for the repository's readout trace.
   * Repository and pinned-Mathlib searches found no existing theorem packaging
     this update-tail equality for `completeItinerary`. -/

namespace D5.S3.ObserverMemory.Trajectories.FutureItineraryShift

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The complete readout itinerary after one state update is the tail of the
current complete itinerary. -/
theorem future_itinerary_shift {X B : Type*}
    (update : X -> X) (readout : X -> B) (state : X) :
    completeItinerary update readout (update state) =
      Stream'.tail (completeItinerary update readout state) := by
  funext n
  simpa only [completeItinerary, Stream'.tail, Stream'.get] using
    congrArg readout (Function.iterate_succ_apply (f := update) n state).symm

-- A two-state update witnesses that the quantified state carrier can be nontrivial.
example :
    completeItinerary not id (not false) =
      Stream'.tail (completeItinerary not id false) := by
  exact future_itinerary_shift not id false

#print axioms future_itinerary_shift

end D5.S3.ObserverMemory.Trajectories.FutureItineraryShift

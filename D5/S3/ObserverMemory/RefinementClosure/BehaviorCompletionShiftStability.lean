/- GID: D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionShiftStability
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RefinementClosure/BehaviorCompletionShiftStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Behavior completion intertwines the source update with the realized itinerary shift. -/

import D5.S3.ObserverMemory.Trajectories.FutureItineraryShift

/- Library-search audit trail (2026-08-26):
   * Exact family hit `future_itinerary_shift` supplies the complete-word tail
     equality and is applied directly as the first public clause.
   * Exact family primitives `completeItinerary`, `ItineraryRange`, and
     `itineraryUpdate` construct the completion carrier and its restricted shift.
   * `behavior_completion_has_unique_induced_update` proves a stronger abstract
     uniqueness result but does not publicly name the shift or the word equality.
     Repository and pinned-Mathlib searches found no theorem exposing both clauses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionShiftStability

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.Trajectories.FutureItineraryShift

/-- Complete future words shift after one source update, and the same shift
restricts to the realized completion range as its induced dynamics. -/
theorem behavior_completion_shift_stability
    {X B : Type*} (F : X -> X) (q : X -> B) :
    (forall state,
      completeItinerary F q (F state) =
        Stream'.tail (completeItinerary F q state)) ∧
      Set.rangeFactorization (completeItinerary F q) ∘ F =
        itineraryUpdate F q ∘
          Set.rangeFactorization (completeItinerary F q) := by
  constructor
  · exact future_itinerary_shift F q
  · funext state
    apply Subtype.ext
    funext n
    simp [itineraryUpdate, completeItinerary, Function.iterate_succ_apply]

#print axioms behavior_completion_shift_stability

end D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionShiftStability

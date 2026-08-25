/- GID: D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionUniqueStability
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RefinementClosure/BehaviorCompletionUniqueStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The completed behavior range has a unique induced source update. -/

import D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/- Library-search audit trail (2026-08-25):
   * Exact family hits `completeItinerary`, `ItineraryRange`, and
     `itineraryUpdate` supply the source completion, its realized carrier, and
     the canonical restricted shift; they are reused without redeclaration.
   * The frozen predecessor only proves existence under an unused surjectivity
     premise and therefore is not imported or redeclared here.
   * Exact pinned-Mathlib hit `Set.rangeFactorization_surjective` supplies the
     uniqueness step by right cancellation. Repository and pinned-Mathlib
     searches found no exact public theorem for the full exists-unique square. -/

namespace D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionUniqueStability

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The update induced on the realized complete-itinerary range exists
uniquely and makes the canonical range-factorization square commute. -/
theorem behavior_completion_has_unique_induced_update
    {X B : Type*} (F : X -> X) (q : X -> B) :
    ∃! induced : ItineraryRange F q -> ItineraryRange F q,
      Set.rangeFactorization (completeItinerary F q) ∘ F =
        induced ∘ Set.rangeFactorization (completeItinerary F q) := by
  refine ⟨itineraryUpdate F q, ?_, ?_⟩
  · funext x
    apply Subtype.ext
    funext n
    simp [itineraryUpdate, completeItinerary, Function.iterate_succ_apply]
  · intro induced hinduced
    apply Set.rangeFactorization_surjective.injective_comp_right
    exact hinduced.symm.trans (by
      funext x
      apply Subtype.ext
      funext n
      simp [itineraryUpdate, completeItinerary, Function.iterate_succ_apply])

#print axioms behavior_completion_has_unique_induced_update

end D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionUniqueStability

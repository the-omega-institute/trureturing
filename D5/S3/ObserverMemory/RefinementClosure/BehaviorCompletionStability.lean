/- GID: D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionStability
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RefinementClosure/BehaviorCompletionStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The effective behavior completion carries the canonical shift update. -/

import D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/- Library-search audit trail (2026-08-25):
   * Exact family hits `completeItinerary`, `ItineraryRange`, and
     `itineraryUpdate` supply the source completion, its effective carrier, and
     the canonical restricted left shift; they are reused without redeclaration.
   * `BehaviorCompletionCharacterization` and `CanonicalMinimalRealization`
     contain private versions of the needed commutation calculation, so neither
     offers a public declaration to which this atom can bind.
   * Repository and pinned-Mathlib searches for a public range-factorization
     semiconjugacy theorem found no exact hit. The proof below only computes the
     imported shift on the canonical effective-image projection. -/

namespace D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionStability

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The effective image of the complete future itinerary is stable under the
source update, with the imported itinerary shift as induced dynamics. -/
theorem behavior_completion_is_stable
    {X B : Type*} (F : X -> X) (q : X -> B)
    (q_surjective : Function.Surjective q) :
    ∃ induced : ItineraryRange F q -> ItineraryRange F q,
      Set.rangeFactorization (completeItinerary F q) ∘ F =
        induced ∘ Set.rangeFactorization (completeItinerary F q) := by
  have _q_has_effective_codomain : Set.range q = Set.univ :=
    q_surjective.range_eq
  refine ⟨itineraryUpdate F q, ?_⟩
  funext x
  apply Subtype.ext
  funext n
  simp [itineraryUpdate, completeItinerary, Function.iterate_succ_apply]

#print axioms behavior_completion_is_stable

end D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionStability

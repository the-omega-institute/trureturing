/- GID: D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionTranslation
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RefinementClosure/BehaviorCompletionTranslation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A system translation induces a unique map between behavior completions. -/

import D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionFunctoriality

/- Library-search audit trail (2026-08-26):
   * Exact family hits `completeItinerary`, `ItineraryRange`, and
     `completionTransport` supply the canonical completion carriers and induced map.
   * The frozen `behavior_completion_is_functorial` theorem proves the commuting
     square and uniqueness as its first two public clauses, and is applied below.
   * That theorem also exposes shift, identity, and composition clauses, so it is
     not an exact whole-statement bind for this existence-and-uniqueness atom.
-/

namespace D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionTranslation

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionFunctoriality

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Every semiconjugacy whose readout factors through a readout translation
induces a unique map between the corresponding realized itinerary ranges. -/
theorem behavior_completion_translation
    {X Y B R : Type*}
    (F : X -> X) (q : X -> B)
    (G : Y -> Y) (r : Y -> R)
    (h : X -> Y) (eta : B -> R)
    (hstep : Function.Semiconj h F G)
    (hreadout : forall x, r (h x) = eta (q x)) :
    ∃! induced : ItineraryRange F q -> ItineraryRange G r,
      Set.rangeFactorization (completeItinerary G r) ∘ h =
        induced ∘ Set.rangeFactorization (completeItinerary F q) := by
  have laws := behavior_completion_is_functorial
    F q G r G r h eta id id hstep Function.Semiconj.id_left hreadout
      (fun _ => rfl)
  exact ⟨completionTransport F q G r h eta hstep hreadout,
    laws.1, fun candidate candidate_natural =>
      laws.2.1 candidate candidate_natural⟩

#print axioms behavior_completion_translation

end D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionTranslation

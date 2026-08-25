/- GID: D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionFunctoriality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RefinementClosure/BehaviorCompletionFunctoriality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Behavior completion transports system semiconjugacies functorially. -/

import D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/- Library-search audit trail (2026-08-25):
   * Exact family hits `completeItinerary`, `ItineraryRange`, and
     `itineraryUpdate` supply the completion carrier and its canonical shift;
     they are imported rather than redeclared.
   * `BehaviorCompletionReflection` is object-level, while
     `CanonicalMapIdentityComposition` fixes one source update and only varies
     readouts. Neither constructs transport between two dynamical systems.
   * Exact pinned-Mathlib hits `Function.Semiconj.iterate_right`,
     `Function.Semiconj.trans`, and `Set.rangeFactorization_surjective` supply
     iterate transport, composition, and uniqueness. No library theorem
     packages the induced map on realized itinerary ranges. -/

namespace D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionFunctoriality

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A legal system translation transports every realized future itinerary
coordinatewise through its readout translation. -/
def completionTransport
    {X Y B R : Type*}
    (F : X -> X) (q : X -> B) (G : Y -> Y) (r : Y -> R)
    (h : X -> Y) (eta : B -> R)
    (hstep : Function.Semiconj h F G)
    (hreadout : forall x, r (h x) = eta (q x)) :
    ItineraryRange F q -> ItineraryRange G r :=
  fun itinerary =>
    ⟨fun n => eta (itinerary.1 n), by
      rcases itinerary.2 with ⟨x, hx⟩
      refine ⟨h x, ?_⟩
      funext n
      calc
        completeItinerary G r (h x) n =
            r (h ((F^[n]) x)) := by
          exact congrArg r ((hstep.iterate_right n).eq x).symm
        _ = eta (q ((F^[n]) x)) := hreadout ((F^[n]) x)
        _ = eta (itinerary.1 n) := congrArg eta (congrFun hx n)⟩

/-- Observer completion sends legal system translations to their unique
natural maps, preserves the completed shifts, and obeys identity and
composition. -/
theorem behavior_completion_is_functorial
    {X Y Z B R S : Type*}
    (F : X -> X) (q : X -> B)
    (G : Y -> Y) (r : Y -> R)
    (H : Z -> Z) (s : Z -> S)
    (h : X -> Y) (eta : B -> R)
    (k : Y -> Z) (theta : R -> S)
    (hstep : Function.Semiconj h F G)
    (kstep : Function.Semiconj k G H)
    (hreadout : forall x, r (h x) = eta (q x))
    (kreadout : forall y, s (k y) = theta (r y)) :
    (Set.rangeFactorization (completeItinerary G r) ∘ h =
      completionTransport F q G r h eta hstep hreadout ∘
        Set.rangeFactorization (completeItinerary F q)) ∧
    (forall candidate : ItineraryRange F q -> ItineraryRange G r,
      Set.rangeFactorization (completeItinerary G r) ∘ h =
          candidate ∘ Set.rangeFactorization (completeItinerary F q) ->
        candidate = completionTransport F q G r h eta hstep hreadout) ∧
    Function.Semiconj
      (completionTransport F q G r h eta hstep hreadout)
      (itineraryUpdate F q) (itineraryUpdate G r) ∧
    completionTransport F q F q id id Function.Semiconj.id_left
        (fun _ => rfl) = id ∧
    completionTransport F q H s (k ∘ h) (theta ∘ eta)
        (hstep.trans kstep)
        (fun x => (kreadout (h x)).trans (congrArg theta (hreadout x))) =
      completionTransport G r H s k theta kstep kreadout ∘
        completionTransport F q G r h eta hstep hreadout := by
  have projection_natural :
      Set.rangeFactorization (completeItinerary G r) ∘ h =
        completionTransport F q G r h eta hstep hreadout ∘
          Set.rangeFactorization (completeItinerary F q) := by
    funext x
    apply Subtype.ext
    funext n
    change r ((G^[n]) (h x)) = eta (q ((F^[n]) x))
    calc
      r ((G^[n]) (h x)) = r (h ((F^[n]) x)) :=
        congrArg r ((hstep.iterate_right n).eq x).symm
      _ = eta (q ((F^[n]) x)) := hreadout ((F^[n]) x)
  refine ⟨projection_natural, ?_, ?_, ?_, ?_⟩
  · intro candidate candidate_natural
    apply Set.rangeFactorization_surjective.injective_comp_right
    exact candidate_natural.symm.trans projection_natural
  · intro itinerary
    apply Subtype.ext
    rfl
  · funext itinerary
    apply Subtype.ext
    rfl
  · funext itinerary
    apply Subtype.ext
    rfl

#print axioms completionTransport
#print axioms behavior_completion_is_functorial

end D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionFunctoriality

/- GID: D5/S3/ObserverMemory/Trajectories/CompletionExtensivity
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/CompletionExtensivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The current readout factors uniquely through its realized complete itinerary. -/

import D5.S3.ObserverMemory.Trajectories.CurrentReadoutRecovery

/- Library-search audit trail (2026-08-24):
   * Exact repository hits `completeItinerary`, `ItineraryRange`, and
     `recover_current_readout` supply the canonical completion carrier and
     the time-zero factorization; they are imported and applied directly.
   * Exact pinned-Mathlib hits `Set.rangeFactorization`,
     `Set.rangeFactorization_surjective`, and
     `Function.Surjective.injective_comp_right` expose the realized image
     and prove uniqueness by cancellation.
   * Repository and pinned-Mathlib searches found no theorem already
     packaging this factorization with its unique effective-image map. -/

namespace D5.S3.ObserverMemory.Trajectories.CompletionExtensivity

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.Trajectories.CurrentReadoutRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Every readout factors uniquely through the effective image of its
complete future itinerary. -/
theorem completion_extensivity {X B : Type*}
    (F : X -> X) (q : X -> B) :
    ∃! factor : ItineraryRange F q -> B,
      q = factor ∘ Set.rangeFactorization (completeItinerary F q) := by
  let factor : ItineraryRange F q -> B := fun itinerary => itinerary.1 0
  have hfactor :
      q = factor ∘ Set.rangeFactorization (completeItinerary F q) := by
    calc
      q = itineraryHead ∘ completeItinerary F q := recover_current_readout F q
      _ = factor ∘ Set.rangeFactorization (completeItinerary F q) := by
        funext state
        rfl
  refine ⟨factor, hfactor, ?_⟩
  intro candidate hcandidate
  apply Set.rangeFactorization_surjective.injective_comp_right
  exact hcandidate.symm.trans hfactor

/-- A two-state system witnesses that the quantified source carrier can be
nontrivial. -/
example :
    ∃! factor : ItineraryRange (id : Bool -> Bool) id -> Bool,
      (id : Bool -> Bool) =
        factor ∘ Set.rangeFactorization
          (completeItinerary (id : Bool -> Bool) id) := by
  exact completion_extensivity id id

#print axioms completion_extensivity

end D5.S3.ObserverMemory.Trajectories.CompletionExtensivity

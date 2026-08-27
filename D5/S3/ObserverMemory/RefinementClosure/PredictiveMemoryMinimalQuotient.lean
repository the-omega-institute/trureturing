/- GID: D5/S3/ObserverMemory/RefinementClosure/PredictiveMemoryMinimalQuotient
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RefinementClosure/PredictiveMemoryMinimalQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every exact predictive memory maps uniquely onto the completed kernel quotient. -/

import D5.S3.ObserverMemory.PredictionFactors.PredictionCompletionUniversality
import D5.S3.ObserverMemory.Refinement.PredictionCompletion
import Mathlib.Data.Set.Image

/- Library-search audit trail (2026-08-27):
   * The exact family primitive `completeItinerary` constructs the full future
     readout, while `CompletedState` and `completionProjection` expose its
     canonical kernel quotient and projection; none is redeclared here.
   * `prediction_completion_universality` is applied directly to derive the
     future profile from the two public predictive-memory premises.
   * `behavior_completion_is_least_stable_refinement` is not an exact hit: it
     adds source-readout and memory surjectivity and targets the itinerary range.
     `minimal_prediction_belief_state` instead assumes the completed profile
     already factors and omits the source's two separate memory clauses.
   * Pinned Mathlib supplies `Set.rangeSplitting`,
     `Set.apply_rangeSplitting`, `Set.rangeFactorization_surjective`, and the
     quotient soundness rule used to construct and identify the unique factor. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.RefinementClosure.PredictiveMemoryMinimalQuotient

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.PredictionFactors.PredictionCompletionUniversality
open D5.S3.ObserverMemory.Refinement.PredictionCompletion

/-- If the current readout and source update both descend through a memory
interface, that memory's realized image has a unique factor onto the canonical
quotient by equality of all future readouts. -/
theorem predictive_memory_minimal_quotient
    {X B M : Type*} (F : X -> X) (q : X -> B) (r : X -> M)
    (readout_factors : ∃ factor : M -> B, q = factor ∘ r)
    (update_factors : ∃ induced : M -> M, r ∘ F = induced ∘ r) :
    ∃! theta : Set.range r -> CompletedState F q,
      completionProjection F q = theta ∘ Set.rangeFactorization r := by
  rcases readout_factors with ⟨factor, hfactor⟩
  rcases update_factors with ⟨induced, hinduced⟩
  rcases prediction_completion_universality F q r induced factor
      hinduced hfactor with ⟨completion, hcompletion⟩
  let theta : Set.range r -> CompletedState F q := fun memory =>
    completionProjection F q (Set.rangeSplitting r memory)
  have theta_factors :
      completionProjection F q = theta ∘ Set.rangeFactorization r := by
    funext state
    apply Quotient.sound'
    change completeItinerary F q state =
      completeItinerary F q
        (Set.rangeSplitting r (Set.rangeFactorization r state))
    rw [hcompletion]
    exact congrArg completion
      (Set.apply_rangeSplitting r (Set.rangeFactorization r state)).symm
  refine ⟨theta, theta_factors, ?_⟩
  intro candidate candidate_factors
  apply Set.rangeFactorization_surjective.injective_comp_right
  exact candidate_factors.symm.trans theta_factors

#print axioms predictive_memory_minimal_quotient

end D5.S3.ObserverMemory.RefinementClosure.PredictiveMemoryMinimalQuotient

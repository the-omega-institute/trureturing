/- GID: D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionMinimality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RefinementClosure/BehaviorCompletionMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Behavior completion is the least stable refinement of a readout interface. -/

import D5.S3.ObserverMemory.PredictionFactors.PredictionCompletionUniversality

/- Library-search audit trail (2026-08-25):
   * Exact family hit `prediction_completion_universality` factors the full
     future readout through any stable refinement and is applied directly.
     It targets the unrestricted word carrier and proves only existence, so it
     is not an exact hit for the source's effective-image unique factor.
   * The close hit `minimal_deterministic_completion` adds finite-carrier
     hypotheses absent from the source, while `behavior_completion_characterization`
     assumes a stronger universal premise and concludes an equivalence.
   * Exact pinned-Mathlib hits `Set.rangeFactorization` and
     `Function.Surjective.injective_comp_right` restrict the factor to the
     effective completion image and establish its uniqueness.
   * Repository and pinned-Mathlib searches found no theorem already carrying
     the source-general effective-image minimality statement. -/

namespace D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionMinimality

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.PredictionFactors.PredictionCompletionUniversality

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- If a surjective readout interface is stable under the source update and
refines the current readout, then the realized behavior completion factors
uniquely through that interface. -/
theorem behavior_completion_is_least_stable_refinement
    {X B R : Type*}
    (F : X -> X) (q : X -> B) (r : X -> R)
    (q_surjective : Function.Surjective q)
    (r_surjective : Function.Surjective r)
    (r_stable : ∃ induced : R -> R, r ∘ F = induced ∘ r)
    (q_refines_r : ∃! factor : R -> B, q = factor ∘ r) :
    ∃! factor : R -> ItineraryRange F q,
      Set.rangeFactorization (completeItinerary F q) = factor ∘ r := by
  have _q_has_effective_codomain : Set.range q = Set.univ :=
    q_surjective.range_eq
  rcases r_stable with ⟨induced, hinduced⟩
  rcases q_refines_r with ⟨readoutFactor, hreadout, _⟩
  rcases prediction_completion_universality F q r induced readoutFactor
      hinduced hreadout with ⟨completion, hcompletion⟩
  let factor : R -> ItineraryRange F q := fun state =>
    ⟨completion state, by
      rcases r_surjective state with ⟨source, rfl⟩
      exact ⟨source, congrFun hcompletion source⟩⟩
  have hfactor :
      Set.rangeFactorization (completeItinerary F q) = factor ∘ r := by
    funext source
    apply Subtype.ext
    exact congrFun hcompletion source
  refine ⟨factor, hfactor, ?_⟩
  intro candidate hcandidate
  apply r_surjective.injective_comp_right
  exact hcandidate.symm.trans hfactor

#print axioms behavior_completion_is_least_stable_refinement

end D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionMinimality

/- GID: D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionReflection
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RefinementClosure/BehaviorCompletionReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Behavior completion is left adjoint to stable-interface inclusion. -/

import D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionMinimality
import D5.S3.ObserverMemory.Trajectories.BehaviorCompletionExtensivity

/- Library-search audit trail (2026-08-25):
   * Exact family hit `behavior_completion_extensivity` supplies the unit
     factorization from the original readout through its behavior completion.
   * Exact family hit `behavior_completion_is_least_stable_refinement` supplies
     the universal factor from every stable effective interface to completion.
   * The close hit `target_closure_reflection_universal` concerns a different
     target-sufficiency construction, so it is not carrier-faithful here.
   * Repository and pinned-Mathlib searches found no theorem already stating
     this behavior-completion iff. The proof composes the two exact family
     factors and uses `Function.Surjective.injective_comp_right` for uniqueness. -/

namespace D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionReflection

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionMinimality
open D5.S3.ObserverMemory.Trajectories.BehaviorCompletionExtensivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- For a stable interface onto its effective codomain, behavior completion
refines that interface exactly when the original readout does. -/
theorem behavior_completion_reflection
    {X B R : Type*}
    (F : X -> X) (q : X -> B) (r : X -> R)
    (q_surjective : Function.Surjective q)
    (r_surjective : Function.Surjective r)
    (r_stable : ∃ induced : R -> R, r ∘ F = induced ∘ r) :
    (∃! completionFactor : R -> ItineraryRange F q,
      Set.rangeFactorization (completeItinerary F q) = completionFactor ∘ r) ↔
    (∃! readoutFactor : R -> B, q = readoutFactor ∘ r) := by
  constructor
  · rintro ⟨completionFactor, completion_factors, _⟩
    rcases behavior_completion_extensivity F q with
      ⟨currentReadout, current_factors, _⟩
    let readoutFactor : R -> B := currentReadout ∘ completionFactor
    have readout_factors : q = readoutFactor ∘ r := by
      calc
        q = currentReadout ∘
            Set.rangeFactorization (completeItinerary F q) := current_factors
        _ = (currentReadout ∘ completionFactor) ∘ r := by
          rw [completion_factors]
          rfl
        _ = readoutFactor ∘ r := rfl
    refine ⟨readoutFactor, readout_factors, ?_⟩
    intro candidate candidate_factors
    apply r_surjective.injective_comp_right
    exact candidate_factors.symm.trans readout_factors
  · intro q_refines_r
    exact behavior_completion_is_least_stable_refinement
      F q r q_surjective r_surjective r_stable q_refines_r

#print axioms behavior_completion_reflection

end D5.S3.ObserverMemory.RefinementClosure.BehaviorCompletionReflection

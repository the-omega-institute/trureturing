/- GID: D5/S3/ObserverMemory/PredictionFactors/PredictionCompletionUniversality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionFactors/PredictionCompletionUniversality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compatible coarse dynamics determine the complete future readout. -/

import D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/- Library-search audit trail (2026-08-20):
   * Repository search found `completeItinerary`, the exact source-semantics primitive for the
     full future trace, but no theorem stating its factorization through a compatible coarse map.
   * Pinned Mathlib grep found `Function.semiconj_iff_comp_eq` and the exact iterate transport
     theorem `Function.Semiconj.iterate_right`; both are applied below.
   * Repository and pinned-Mathlib searches for a theorem constructing the displayed factor map
     from both source equations found no equal or stronger full-statement result. -/

namespace D5.S3.ObserverMemory.PredictionFactors.PredictionCompletionUniversality

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A coarse state map that intertwines the dynamics and factors the current readout also
factors the complete future trace. -/
theorem prediction_completion_universality
    {X B C : Type*}
    (sourceStep : X -> X) (readout : X -> B) (coarseState : X -> C)
    (coarseStep : C -> C) (coarseReadout : C -> B)
    (step_factors : coarseState ∘ sourceStep = coarseStep ∘ coarseState)
    (readout_factors : readout = coarseReadout ∘ coarseState) :
    exists completion : C -> (Nat -> B),
      completeItinerary sourceStep readout = completion ∘ coarseState := by
  have hSemiconj : Function.Semiconj coarseState sourceStep coarseStep :=
    Function.semiconj_iff_comp_eq.mpr step_factors
  refine ⟨fun c n => coarseReadout ((coarseStep^[n]) c), ?_⟩
  funext x n
  calc
    completeItinerary sourceStep readout x n =
        coarseReadout (coarseState ((sourceStep^[n]) x)) := by
      change readout ((sourceStep^[n]) x) = _
      exact congrFun readout_factors ((sourceStep^[n]) x)
    _ = coarseReadout ((coarseStep^[n]) (coarseState x)) :=
      congrArg coarseReadout ((hSemiconj.iterate_right n).eq x)
    _ = ((fun c n => coarseReadout ((coarseStep^[n]) c)) ∘ coarseState) x n := rfl

#print axioms prediction_completion_universality

end D5.S3.ObserverMemory.PredictionFactors.PredictionCompletionUniversality

/- GID: D5/S3/ObserverMemory/Refinement/PredictionCompletionIdempotence
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Refinement/PredictionCompletionIdempotence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Predictive completion has the identity future relation and is idempotent. -/

import D5.S3.ObserverMemory.Refinement.CascadeCompletion

/- Library-search audit trail (2026-08-20):
   * The repository exact hit `cascade_completion` identifies a second-stage
     quotient with the direct completion; it is specialized and applied below.
   * The repository exact hit `second_stage_relation_projection` identifies
     the second-stage relation on representatives; it is applied below.
   * Pinned Mathlib exact hits `Quotient.inductionOn₂'` and `Quotient.eq`
     extend that representative calculation to all completed states.
   * Repository and pinned-Mathlib shape searches found no theorem packaging
     the identity relation and the specialized second-completion equivalence
     as the two public clauses below. -/

namespace D5.S3.ObserverMemory.Refinement.PredictionCompletionIdempotence

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.Refinement.PredictionCompletion
open D5.S3.ObserverMemory.Refinement.CascadeCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- After predictive completion, equality of every future readout is equality
of completed states, and quotienting by that relation recovers the same
completed state space. -/
theorem prediction_completion_idempotent {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) :
    (∀ first second : CompletedState update readout,
      secondStageRelation update readout (id : O -> O) first second ↔
        first = second) ∧
      Nonempty
        (Quotient (secondStageRelation update readout (id : O -> O)) ≃
          CompletedState update readout) := by
  have cascade :=
    cascade_completion update readout readout (id : O -> O) rfl
  constructor
  · intro first second
    refine Quotient.inductionOn₂' first second fun y y' => ?_
    change
      secondStageRelation update readout (id : O -> O)
          (completionProjection update readout y)
          (completionProjection update readout y') ↔
        completionProjection update readout y =
          completionProjection update readout y'
    rw [second_stage_relation_projection
      update readout readout (id : O -> O) rfl y y']
    exact Quotient.eq.symm
  · rcases cascade.2.2.2 with ⟨equivalence, _⟩
    exact ⟨equivalence⟩

/-- The generic state and readout carriers admit a concrete singleton
specialization. -/
example :
    Nonempty
      (Quotient
          (secondStageRelation (id : Unit -> Unit)
            (id : Unit -> Unit) (id : Unit -> Unit)) ≃
        CompletedState (id : Unit -> Unit) (id : Unit -> Unit)) :=
  (prediction_completion_idempotent
    (id : Unit -> Unit) (id : Unit -> Unit)).2

#print axioms prediction_completion_idempotent

end D5.S3.ObserverMemory.Refinement.PredictionCompletionIdempotence

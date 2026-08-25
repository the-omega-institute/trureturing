/- GID: D5/S3/ObserverMemory/RefinementDescent/ControlledCompletionDescent
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RefinementDescent/ControlledCompletionDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Controlled updates and readouts descend uniquely to behavior completion. -/

import D5.S3.ObserverMemory.Dynamics.ControlledInterventionDescentUniqueness

/- Library-search audit trail (2026-08-25):
   * Exact family hits `ControlledCompletion`, `completionProjection`,
     `completionUpdate`, and `completionReadout` construct the source quotient
     and its canonical maps; none is redeclared here.
   * The frozen `all_interventions_unique_completion_descent` proves unique
     update descent for every control and is applied directly.
   * Pinned Mathlib quotient hits are supporting primitives, but no existing
     theorem packages both controlled update and readout descent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.RefinementDescent.ControlledCompletionDescent

open D5.S3.ObserverMemory.Dynamics.ControlledInterventionDescentUniqueness
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/-- On the complete controlled-behavior quotient, the canonical update for
each input and the canonical current readout are precisely the unique maps
whose squares commute with the quotient projection. -/
theorem controlled_completion_update_and_readout_descend
    {U Y O : Type*} (update : U -> Y -> Y) (readout : Y -> O) :
    (forall u : U,
      forall descended :
          ControlledCompletion update readout ->
            ControlledCompletion update readout,
        completionProjection update readout ∘ update u =
            descended ∘ completionProjection update readout <->
          descended = completionUpdate update readout u) ∧
      forall descendedReadout : ControlledCompletion update readout -> O,
        readout = descendedReadout ∘ completionProjection update readout <->
          descendedReadout = completionReadout update readout := by
  constructor
  · intro u descended
    have uniqueDescent := all_interventions_unique_completion_descent
      update readout u
    constructor
    · intro descendedSquare
      apply uniqueDescent.unique descendedSquare
      funext state
      rfl
    · rintro rfl
      funext state
      rfl
  · intro descendedReadout
    constructor
    · intro readoutSquare
      funext completed
      rcases Quotient.mk_surjective completed with ⟨state, rfl⟩
      exact (congrFun readoutSquare state).symm
    · rintro rfl
      funext state
      rfl

#print axioms controlled_completion_update_and_readout_descend

end D5.S3.ObserverMemory.RefinementDescent.ControlledCompletionDescent

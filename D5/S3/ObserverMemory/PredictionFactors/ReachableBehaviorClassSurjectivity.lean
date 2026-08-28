/- GID: D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorClassSurjectivity
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionFactors/ReachableBehaviorClassSurjectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every reachable future-behavior class is produced by an allowed action. -/

import D5.S3.ObserverMemory.PredictionFactors.ReachableBehaviorMinimality

/- Library-search audit trail (2026-08-28):
   * Exact repository primitives `ReachableOrbit`, `futureBehavior`,
     `ReachableBehaviorQuotient`, `orbitPoint`, and `behaviorClass` construct the
     source carrier and its canonical classes; they are imported rather than
     redeclared.
   * Repository searches found reachability inside larger minimality proofs, but
     no frozen public theorem asserting surjectivity of `behaviorClass` itself.
   * Exact pinned-Mathlib hit `Quotient.mk_surjective` supplies quotient
     surjectivity. No library theorem packages the source-specific orbit map. -/

namespace D5.S3.ObserverMemory.PredictionFactors.ReachableBehaviorClassSurjectivity

open D5.S3.ObserverMemory.PredictionFactors.ReachableBehaviorMinimality

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Every class of the reachable future-behavior quotient is represented by
the state produced from the actual anchor by some allowed action. -/
theorem every_reachable_behavior_class_is_reachable
    {M X B : Type*} [Monoid M] [MulAction M X]
    (anchor : X) (readout : X -> B) :
    Function.Surjective
      (behaviorClass (M := M) (X := X) (B := B) anchor readout) := by
  intro behavior
  obtain ⟨reachable_state, rfl⟩ := Quotient.mk_surjective behavior
  rcases reachable_state with ⟨state, action, action_reaches_state⟩
  refine ⟨action, ?_⟩
  change Quotient.mk _ (orbitPoint anchor action) =
    Quotient.mk _ ⟨state, ⟨action, action_reaches_state⟩⟩
  apply Quotient.sound
  exact congrArg (futureBehavior (M := M) anchor readout)
    (Subtype.ext action_reaches_state)

#print axioms every_reachable_behavior_class_is_reachable

end D5.S3.ObserverMemory.PredictionFactors.ReachableBehaviorClassSurjectivity

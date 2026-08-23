/- GID: D5/S3/ConceptDynamics/Coding/PartitionManipulation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PartitionManipulation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Homogeneous message fibers admit correct defaults and preclude manipulation. -/

import D5.S0.Rewriting.Quotients.AnswerabilityCriterion

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'manipulation_needs_heterogeneous_fiber' D5 Golden/Frozen/accepted`
     returned no matches.
   * Searches for heterogeneous fibers, omissions, lossless encodings, and targets found
     `AnswerabilityCriterion.answerability_criterion`, whose first equivalence supplies
     the more general factorization theorem used below. The anticipated 239.1 module is
     not visible on this branch.
   * `heterogeneous_fiber_forces_misclassification` proves the adjacent converse pressure:
     two target values in one fiber force every deterministic rule to err somewhere. It
     has neither the manipulation definition nor the specified actual-state witness.
   * The proof specializes the upstream factorization to construct a correct default,
     then uses its pointwise correctness to rule out manipulation. The Boolean smoke test
     independently supplies an actual manipulation witness.
   -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding

/-- A sender manipulates a partition at `actual` when its true message has a
target-heterogeneous fiber and the receiver's default target is wrong there. -/
def PartitionManipulation {X M Tval : Type*} (message : X -> M) (target : X -> Tval)
    (delta : M -> Tval) (actual : X) : Prop :=
  (exists other, message other = message actual /\ target other ≠ target actual) /\
    delta (message actual) ≠ target actual

namespace PartitionManipulation

/-- If every message fiber is target-homogeneous, one can choose a default rule that is
correct on every realized message; partition manipulation is then impossible everywhere. -/
theorem manipulation_needs_heterogeneous_fiber {X M Tval : Type*} [Nonempty X]
    (message : X -> M) (target : X -> Tval)
    (homogeneous : forall a b, message a = message b -> target a = target b) :
    exists delta : M -> Tval,
      (forall actual, delta (message actual) = target actual) /\
        forall actual, ¬PartitionManipulation message target delta actual := by
  let anchor : X := Classical.choice inferInstance
  obtain ⟨delta, factors⟩ :=
    ((D5.S0.Rewriting.Quotients.AnswerabilityCriterion.answerability_criterion
      anchor message target).1).mpr homogeneous
  have correct (actual : X) : delta (message actual) = target actual := by
    rw [factors]
    rfl
  exact ⟨delta, correct, fun actual manipulation => manipulation.2 (correct actual)⟩

example :
    PartitionManipulation (fun _ : Bool => ()) (id : Bool -> Bool)
      (fun _ : Unit => false) true := by
  constructor
  · exact ⟨false, rfl, Bool.false_ne_true⟩
  · exact Bool.false_ne_true

#print axioms manipulation_needs_heterogeneous_fiber

end PartitionManipulation

end D5.S3.ConceptDynamics.Coding

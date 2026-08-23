/- GID: D5/S3/ConceptDynamics/Communication/HeterogeneousFiberMisclassification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Communication/HeterogeneousFiberMisclassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A message fiber with two target values forces a deterministic error. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition

/- Library-search audit trail (2026-08-22):
   * Exact repository hit `Concept` is the canonical readout primitive and is
     imported from `ConceptFiberDecomposition` rather than redeclared.
   * Exact pinned logic hits `not_or` and `not_ne_iff`, together with core
     `congrArg`, turn simultaneous correctness into equality of the two targets.
   * Searches for heterogeneous fibers, deterministic inference, and pointwise
     misclassification found no theorem with this two-state error disjunction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Communication.HeterogeneousFiberMisclassification

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- If one message fiber contains two different target values, every
deterministic inference rule is wrong at one of those two states. -/
theorem heterogeneous_fiber_forces_misclassification
    {X Message Target : Type*}
    (message : Concept X Message) (target : Concept X Target)
    (x y : X)
    (heterogeneousFiber : message x = message y ∧ target x ≠ target y) :
    ∀ inference : Message -> Target,
      inference (message x) ≠ target x ∨
        inference (message y) ≠ target y := by
  intro inference
  classical
  by_contra bothCorrect
  simp only [not_or, not_ne_iff] at bothCorrect
  apply heterogeneousFiber.2
  calc
    target x = inference (message x) := bothCorrect.1.symm
    _ = inference (message y) := congrArg inference heterogeneousFiber.1
    _ = target y := bothCorrect.2

/-- A constant message and identity Boolean target realize the theorem's
heterogeneous-fiber premise. -/
example :
    ∀ inference : Unit -> Bool,
      inference ((fun _ : Bool => ()) false) ≠ (id : Bool -> Bool) false ∨
        inference ((fun _ : Bool => ()) true) ≠ (id : Bool -> Bool) true := by
  exact heterogeneous_fiber_forces_misclassification
    (fun _ : Bool => ()) id false true ⟨rfl, Bool.false_ne_true⟩

#print axioms heterogeneous_fiber_forces_misclassification

end D5.S3.ConceptDynamics.Communication.HeterogeneousFiberMisclassification

/- GID: D5/S3/ConceptDynamics/Fibers/CanonicalDependentFiberEquivalence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Fibers/CanonicalDependentFiberEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical dependent-fiber equivalence records a readout and recovers its source. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition

/- Library-search audit trail (2026-08-22):
   * `rg -n 'ConceptFiber|sigma.*fiber|fiber.*equiv' D5` found the family
     source of truth `D5.S3.ConceptDynamics.ConceptFiberDecomposition`, whose
     `Concept` and proof-relevant `ConceptFiber` carriers are imported below.
   * `rg -n 'sigmaFiberEquiv' .lake/packages/mathlib/Mathlib` found the exact
     choice-free primitive `Equiv.sigmaFiberEquiv` in
     `Mathlib.Logic.Equiv.Sum`; it is applied directly in the construction.
   * The accepted sibling `WholeDependentFiberForm` hides its construction
     behind `Nonempty`, so it cannot expose the canonical map required here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Fibers.CanonicalDependentFiberEquivalence

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- The canonical map sends an object to its readout and its proof-relevant
position in the corresponding fiber. -/
def canonicalDependentFiberEquiv
    {X B : Type _} (q : Concept X B) :
    X ≃ Σ b : B, ConceptFiber q b where
  toFun x :=
    let z := (Equiv.sigmaFiberEquiv q).symm x
    ⟨z.1, ⟨z.2.1, z.2.2⟩⟩
  invFun z := Equiv.sigmaFiberEquiv q ⟨z.1, ⟨z.2.1, z.2.2⟩⟩
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨b, x, h⟩
    cases h
    rfl

/-- The canonical dependent-fiber equivalence computes by recording the
readout, and its inverse forgets that record. -/
theorem whole_dependent_fiber_form
    {X B : Type _} (q : Concept X B) :
    (∀ x : X,
      canonicalDependentFiberEquiv q x = ⟨q x, ⟨x, rfl⟩⟩) ∧
    (∀ z : Σ b : B, ConceptFiber q b,
      (canonicalDependentFiberEquiv q).symm z = z.2.1) := by
  constructor
  · intro x
    rfl
  · intro z
    rfl

#print axioms canonicalDependentFiberEquiv
#print axioms whole_dependent_fiber_form

end D5.S3.ConceptDynamics.Fibers.CanonicalDependentFiberEquivalence

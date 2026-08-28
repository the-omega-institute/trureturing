/- GID: D5/S3/ConceptDynamics/Fibers/CanonicalAdmissibleFiberDecomposition
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Fibers/CanonicalAdmissibleFiberDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A readout decomposes all states and admissible states into dependent fibers. -/

import D5.S3.ConceptDynamics.Fibers.CanonicalDependentFiberEquivalence

/- Library-search audit trail (2026-08-27):
   * The body-shape search for `fun x => q x = b` found the canonical carriers
     `Concept` and `ConceptFiber` in `ConceptFiberDecomposition`; they are reused.
   * The body-shape search for `⟨q x, ⟨x, rfl⟩⟩` found the frozen SSOT
     `CanonicalDependentFiberEquivalence.canonicalDependentFiberEquiv` and its
     public computation theorem; both are imported instead of redeclared.
   * Searches for `AdmissibleConceptFiber`, `PSigma.*Adm`, and admissible
     dependent-fiber equivalences found no D5 declaration.
   * Pinned Mathlib's exact ordinary construction is `Equiv.sigmaFiberEquiv` in
     `Mathlib.Logic.Equiv.Sum`; the frozen canonical SSOT already applies it.
     No pinned theorem packages the additional admissible carrier and both
     computation rules, so only that missing construction is proved here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Fibers.CanonicalAdmissibleFiberDecomposition

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Fibers.CanonicalDependentFiberEquivalence

/-- The residual fiber over `b`, restricted to states satisfying `admissible`. -/
def AdmissibleConceptFiber {X B : Type _} (q : Concept X B)
    (admissible : X -> Prop) (b : B) :=
  PSigma fun x : X => admissible x ∧ q x = b

/-- The ordinary and admissible dependent-fiber decompositions are the unique
equivalences computing by recording the readout and forgetting it again. -/
theorem canonical_admissible_fiber_decomposition
    {X B : Type _} (q : Concept X B) (admissible : X -> Prop) :
    (∃! ordinary : X ≃ Σ b : B, ConceptFiber q b,
      (∀ x : X, ordinary x = ⟨q x, ⟨x, rfl⟩⟩) ∧
        ∀ z : Σ b : B, ConceptFiber q b, ordinary.symm z = z.2.1) ∧
      ∃! restricted : PSigma admissible ≃
          Σ b : B, AdmissibleConceptFiber q admissible b,
        (∀ z : PSigma admissible,
          restricted z = ⟨q z.1, ⟨z.1, z.2, rfl⟩⟩) ∧
          ∀ z : Σ b : B, AdmissibleConceptFiber q admissible b,
            restricted.symm z = ⟨z.2.1, z.2.2.1⟩ := by
  constructor
  · refine ⟨canonicalDependentFiberEquiv q, whole_dependent_fiber_form q, ?_⟩
    intro other hOther
    apply Equiv.ext
    intro x
    exact (hOther.1 x).trans ((whole_dependent_fiber_form q).1 x).symm
  · let restrictedEquiv : PSigma admissible ≃
        Σ b : B, AdmissibleConceptFiber q admissible b :=
      { toFun := fun z => ⟨q z.1, ⟨z.1, z.2, rfl⟩⟩
        invFun := fun z => ⟨z.2.1, z.2.2.1⟩
        left_inv := by
          intro z
          rfl
        right_inv := by
          rintro ⟨b, x, hAdmissible, hReadout⟩
          cases hReadout
          rfl }
    refine ⟨restrictedEquiv, ?_, ?_⟩
    · constructor
      · intro z
        rfl
      · intro z
        rfl
    · intro other hOther
      apply Equiv.ext
      intro z
      simpa [restrictedEquiv] using hOther.1 z

#print axioms AdmissibleConceptFiber
#print axioms canonical_admissible_fiber_decomposition

end D5.S3.ConceptDynamics.Fibers.CanonicalAdmissibleFiberDecomposition

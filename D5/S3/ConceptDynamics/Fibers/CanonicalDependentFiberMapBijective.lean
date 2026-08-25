/- GID: D5/S3/ConceptDynamics/Fibers/CanonicalDependentFiberMapBijective
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Fibers/CanonicalDependentFiberMapBijective
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical map into the dependent fiber sum is bijective. -/

import D5.S3.ConceptDynamics.Fibers.CanonicalDependentFiberEquivalence

/- Library-search audit trail (2026-08-25):
   * The current-tree search for the displayed fiber map and its bijectivity
     found the frozen `CanonicalDependentFiberEquivalence` construction but no
     theorem asserting this proposition.
   * The body-shape search found the family carriers `Concept` and
     `ConceptFiber` in `ConceptFiberDecomposition`; they are reused through the
     frozen predecessor rather than redeclared.
   * Pinned Mathlib's exact construction primitive `Equiv.sigmaFiberEquiv` is
     already used by that predecessor. Its `Equiv.bijective` property is
     applied directly below through the named canonical equivalence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Fibers.CanonicalDependentFiberMapBijective

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Fibers.CanonicalDependentFiberEquivalence

/-- Recording an object's readout together with its reflexive fiber witness is
a bijection onto the full dependent sum of readout fibers. -/
theorem canonical_dependent_fiber_map_bijective
    {X B : Type _} (q : Concept X B) :
    Function.Bijective
      (fun x : X =>
        (⟨q x, ⟨x, rfl⟩⟩ : Σ b : B, ConceptFiber q b)) := by
  exact (canonicalDependentFiberEquiv q).bijective

#print axioms canonical_dependent_fiber_map_bijective

end D5.S3.ConceptDynamics.Fibers.CanonicalDependentFiberMapBijective

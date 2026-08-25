/- GID: D5/S3/ConceptDynamics/RefinementFactorization/InjectiveInterfaceTargetFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementFactorization/InjectiveInterfaceTargetFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An injective interface uniquely factors every target on realized images. -/

import D5.S3.ConceptDynamics.RefinementFactorization.RealizedImageKernelFactorization

/- Library-search audit trail (2026-08-25):
   * Current-tree searches for `TargetImage q.*TargetImage`,
     `canonicalTargetReadout T.*canonicalTargetReadout q`, and
     `rangeFactorization T.*rangeFactorization q` found no exact theorem with the
     injectivity premise and universal target conclusion.
   * Exact repository hit
     `realized_image_unique_factorization_iff_reverse_kernel` gives the unique
     factor on the two realized images exactly from reverse kernel inclusion. It
     is imported and applied directly below.
   * Pinned Mathlib exact hits `Function.Injective.factorsThrough`,
     `Set.rangeFactorization`, `Set.rangeFactorization_surjective`, and
     `Set.rangeFactorization_bijective` provide the underlying general interface
     primitives. The repository theorem already packages their effective-image
     uniqueness, so no parallel factor construction is introduced here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S3.ConceptDynamics.RefinementFactorization.InjectiveInterfaceTargetFactorization

open D5.S3.ConceptDynamics.RefinementFactorization.RealizedImageKernelFactorization

/-- On the realized image of an injective interface, every target has one and only
one factor. Restricting both codomains to their ranges also covers empty state types. -/
theorem injective_interface_factors_every_target
    {X B Y : Type u} (q : X -> B) (T : X -> Y)
    (injective : Function.Injective q) :
    ExistsUnique fun factor : Set.range q -> Set.range T =>
      Set.rangeFactorization T = factor ∘ Set.rangeFactorization q := by
  apply (realized_image_unique_factorization_iff_reverse_kernel T q).2
  intro x y sameInterface
  exact congrArg T (injective sameInterface)

#print axioms injective_interface_factors_every_target

end D5.S3.ConceptDynamics.RefinementFactorization.InjectiveInterfaceTargetFactorization

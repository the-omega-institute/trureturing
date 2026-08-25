/- GID: D5/S3/ObserverMemory/Refinement/InterfaceKernelCriterion
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Refinement/InterfaceKernelCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Interface refinement is equivalent to reverse equality-kernel inclusion. -/

import D5.S3.ObserverMemory.Refinement.EffectiveImageKernelCriterion

/- Library-search audit trail (2026-08-25):
   * Exact observer-family hit
     `refinement_iff_kernel_inclusion_on_effective_images` states both the
     unique effective-image factorization and reverse equality-kernel
     inclusion; it is imported and applied directly.
   * Exact pinned-Mathlib component hits
     `Set.rangeFactorization_eq_rangeFactorization_iff`,
     `Set.rangeSplitting`, and `Set.apply_rangeSplitting` support the imported
     construction without requiring a parallel refinement primitive. -/

namespace D5.S3.ObserverMemory.Refinement.InterfaceKernelCriterion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ObserverMemory.Refinement.EffectiveImageKernelCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A finer interface uniquely determines a coarser interface on their
effective images exactly when its equality kernel is contained in the
coarser equality kernel. -/
theorem interface_refinement_iff_kernel_inclusion
    {X Coarse Fine : Type*}
    (q : Concept X Coarse) (r : Concept X Fine) :
    (∃! factor : Set.range r -> Set.range q,
        ∀ x, factor (Set.rangeFactorization r x) =
          Set.rangeFactorization q x) ↔
      ∀ x y, r x = r y -> q x = q y := by
  exact refinement_iff_kernel_inclusion_on_effective_images q r

#print axioms interface_refinement_iff_kernel_inclusion

end D5.S3.ObserverMemory.Refinement.InterfaceKernelCriterion

/- GID: D5/S3/ConceptDynamics/Factor/UniqueInterfaceKernelCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Factor/UniqueInterfaceKernelCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unique effective-interface factorization is reverse kernel inclusion. -/

import D5.S3.ConceptDynamics.RefinementAlgebra.ObserverStrategyFactorization

/- Library-search audit trail (2026-08-27):
   * Exact family hits `Concept`, `Refines`, and `Setoid.ker` provide the
     canonical interface and equality-kernel primitives.
   * `observer_strategy_factorization` is the direct owner of the existence
     criterion, but its public `Refines` predicate does not expose uniqueness.
   * `realized_image_unique_factorization_iff_reverse_kernel` changes both
     codomains to range subtypes and is therefore not exact for already
     effective declared carriers.
   * Pinned-Mathlib searches found no exact unique-factor criterion on the
     declared carriers. No new `def` or `abbrev` is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Factor.UniqueInterfaceKernelCriterion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.RefinementAlgebra.ObserverStrategyFactorization

universe u

/-- A surjective finer interface admits a unique factor to a coarser readout
exactly when its equality kernel is contained in the coarser kernel. -/
theorem unique_interface_factorization_iff_reverse_kernel
    {X Coarse Fine : Type u}
    (q : Concept X Coarse) (r : Concept X Fine)
    (r_surjective : Function.Surjective r) :
    (∃! factor : Fine → Coarse, q = factor ∘ r) ↔
      Setoid.ker r ≤ Setoid.ker q := by
  have existence := observer_strategy_factorization r q r_surjective
  constructor
  · rintro ⟨factor, hfactor, _⟩
    exact existence.mp ⟨factor, hfactor⟩
  · intro hkernel
    obtain ⟨factor, hfactor⟩ := existence.mpr hkernel
    refine ⟨factor, hfactor, ?_⟩
    intro other hother
    funext observation
    obtain ⟨state, rfl⟩ := r_surjective observation
    exact (congrFun hother state).symm.trans (congrFun hfactor state)

#print axioms unique_interface_factorization_iff_reverse_kernel

end D5.S3.ConceptDynamics.Factor.UniqueInterfaceKernelCriterion

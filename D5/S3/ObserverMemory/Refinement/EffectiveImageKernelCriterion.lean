/- GID: D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Effective-image refinement is equivalent to equality-kernel inclusion. -/

import D5.S3.ObserverMemory.Refinement.FactorizationCategory
import Mathlib.Data.Set.Image

/- Library-search audit trail (2026-08-24):
   * Exact pinned-Mathlib hits `Set.rangeFactorization`,
     `Set.rangeFactorization_eq_rangeFactorization_iff`, `Set.rangeSplitting`,
     and `Set.apply_rangeSplitting` construct and verify the canonical factor
     on the realized images; they are applied directly below.
   * The canonical repository `Concept` carrier is imported from the existing
     refinement family rather than redeclared.
   * Repository hits `answerability_criterion`, `finite_reverse_criterion`,
     and `effective_image_uniqueness` are adjacent existence or uniqueness
     results, but no exact unique range-to-range kernel criterion was found.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Refinement.EffectiveImageKernelCriterion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- On the realized codomains, the finer readout determines the coarser one by
a unique canonical factor exactly when equality under the finer readout always
implies equality under the coarser readout. -/
theorem refinement_iff_kernel_inclusion_on_effective_images
    {X Coarse Fine : Type*}
    (q : Concept X Coarse) (r : Concept X Fine) :
    (∃! factor : Set.range r → Set.range q,
        ∀ x, factor (Set.rangeFactorization r x) = Set.rangeFactorization q x) ↔
      ∀ x y, r x = r y → q x = q y := by
  constructor
  · rintro ⟨factor, hfactor, _⟩ x y hxy
    have hfactor_xy := congrArg factor
      ((Set.rangeFactorization_eq_rangeFactorization_iff x y).mpr hxy)
    have hq_range :
        Set.rangeFactorization q x = Set.rangeFactorization q y := by
      rw [← hfactor x, ← hfactor y]
      exact hfactor_xy
    exact (Set.rangeFactorization_eq_rangeFactorization_iff x y).mp hq_range
  · intro hkernel
    let factor : Set.range r → Set.range q := fun value =>
      Set.rangeFactorization q (Set.rangeSplitting r value)
    have hfactor :
        ∀ x, factor (Set.rangeFactorization r x) = Set.rangeFactorization q x := by
      intro x
      apply (Set.rangeFactorization_eq_rangeFactorization_iff _ _).mpr
      exact hkernel _ _ (by
        exact Set.apply_rangeSplitting r (Set.rangeFactorization r x))
    refine ⟨factor, hfactor, ?_⟩
    intro other hother
    funext value
    obtain ⟨x, hx⟩ := value.property
    have hvalue : Set.rangeFactorization r x = value := Subtype.ext hx
    rw [← hvalue, hother x, hfactor x]

#print axioms refinement_iff_kernel_inclusion_on_effective_images

end D5.S3.ObserverMemory.Refinement.EffectiveImageKernelCriterion

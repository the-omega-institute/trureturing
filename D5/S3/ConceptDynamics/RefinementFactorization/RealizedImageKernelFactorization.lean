/- GID: D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Realized-image factorization is unique exactly under reverse kernel inclusion. -/

import D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality
import Mathlib.Data.Set.Image

/- Library-search audit trail (2026-08-24):
   * Exact current-tree hit
     `ConceptKernelOrderDuality.effective_refines_iff_reverse_kernel` is the
     canonical family-owned existence criterion; it is imported and applied to
     the two `Set.rangeFactorization` readouts below.
   * Exact pinned-Mathlib hits `Set.rangeFactorization`,
     `Set.rangeFactorization_surjective`, and
     `Set.rangeFactorization_eq_rangeFactorization_iff` supply the effective
     images, uniqueness, and identification with the original readout kernels.
   * The frozen predecessor `EffectiveImageKernelCriterion` has the same public
     realized-image shape but reconstructs the kernel criterion independently;
     it remains unchanged while this module contributes only the canonical bridge.
   * Searches for `rangeFactorization.*kernel`, `kernel.*rangeFactorization`, and
     unique range-factorization criteria found no other exact theorem. The
     `loogle` and `leansearch` executables are absent from PATH on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementFactorization.RealizedImageKernelFactorization

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality

universe u

/-- The readout on the realized finer image has a unique factor to the realized
coarser image exactly when the finer equality kernel is contained in the coarser
one. -/
theorem realized_image_unique_factorization_iff_reverse_kernel
    {X Coarse Fine : Type u} (q : Concept X Coarse) (r : Concept X Fine) :
    (∃! factor : Set.range r → Set.range q,
        Set.rangeFactorization q = factor ∘ Set.rangeFactorization r) ↔
      Setoid.ker r ≤ Setoid.ker q := by
  let qEffective : EffectiveConcept X := {
    Coordinate := Set.range q
    readout := Set.rangeFactorization q
    effective := Set.rangeFactorization_surjective }
  let rEffective : EffectiveConcept X := {
    Coordinate := Set.range r
    readout := Set.rangeFactorization r
    effective := Set.rangeFactorization_surjective }
  have canonical := effective_refines_iff_reverse_kernel qEffective rEffective
  have qKernel : Setoid.ker (Set.rangeFactorization q) = Setoid.ker q := by
    ext x y
    exact Set.rangeFactorization_eq_rangeFactorization_iff x y
  have rKernel : Setoid.ker (Set.rangeFactorization r) = Setoid.ker r := by
    ext x y
    exact Set.rangeFactorization_eq_rangeFactorization_iff x y
  have existence :
      (∃ factor : Set.range r → Set.range q,
          Set.rangeFactorization q = factor ∘ Set.rangeFactorization r) ↔
        Setoid.ker r ≤ Setoid.ker q := by
    change Refines (Set.rangeFactorization q) (Set.rangeFactorization r) ↔ _
    rw [← qKernel, ← rKernel]
    simpa only [qEffective, rEffective] using canonical
  constructor
  · rintro ⟨factor, hfactor, _⟩
    exact existence.mp ⟨factor, hfactor⟩
  · intro hkernel
    obtain ⟨factor, hfactor⟩ := existence.mpr hkernel
    refine ⟨factor, hfactor, ?_⟩
    intro other hother
    funext value
    obtain ⟨x, rfl⟩ := Set.rangeFactorization_surjective value
    exact (congrFun (hfactor.symm.trans hother) x).symm

example : Concept Bool Bool := id

#print axioms realized_image_unique_factorization_iff_reverse_kernel

end D5.S3.ConceptDynamics.RefinementFactorization.RealizedImageKernelFactorization

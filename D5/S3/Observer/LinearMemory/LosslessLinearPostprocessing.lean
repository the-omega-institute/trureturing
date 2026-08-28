/- GID: D5/S3/Observer/LinearMemory/LosslessLinearPostprocessing
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/LosslessLinearPostprocessing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Kernel preservation characterizes injectivity on the observed range. -/

import Mathlib.LinearAlgebra.Quotient.Basic

/- Library-search audit trail (2026-08-28):
   * Repository searches found only the generic function-fiber theorem
     `LosslessEncodingCriterion.lossless_iff_injective_on_image`; it does not
     state the linear kernel criterion on the source carrier.
   * Pinned Mathlib supplies `LinearMap.ker_comp`, but no exact theorem equates
     preservation of the kernel of a composite with injectivity on the range.
   * No new source primitive is introduced in this module. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.LinearMemory.LosslessLinearPostprocessing

/-- A linear postprocessing preserves exactly the invisible directions of an
observation map precisely when it is injective on the observation's range. -/
theorem kernel_comp_eq_iff_injective_on_range
    {K V Y Z : Type*} [Ring K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup Y] [Module K Y]
    [AddCommGroup Z] [Module K Z]
    (M : V →ₗ[K] Y) (B : Y →ₗ[K] Z) :
    LinearMap.ker (B.comp M) = LinearMap.ker M ↔
      Set.InjOn B (Set.range M) := by
  constructor
  · intro kernelsEqual first firstInRange second secondInRange imagesEqual
    obtain ⟨x, rfl⟩ := firstInRange
    obtain ⟨y, rfl⟩ := secondInRange
    have differenceInCompositeKernel : x - y ∈ LinearMap.ker (B.comp M) := by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, map_sub, map_sub,
        imagesEqual, sub_self]
    have differenceInKernel : x - y ∈ LinearMap.ker M := by
      rwa [kernelsEqual] at differenceInCompositeKernel
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at differenceInKernel
    exact differenceInKernel
  · intro injectiveOnRange
    apply le_antisymm
    · intro x compositeKernel
      rw [LinearMap.mem_ker, LinearMap.comp_apply] at compositeKernel
      rw [LinearMap.mem_ker]
      have sameImage : B (M x) = B (M 0) := by
        simpa using compositeKernel
      have sameObservation := injectiveOnRange
        (Set.mem_range_self x) (Set.mem_range_self 0) sameImage
      simpa using sameObservation
    · exact LinearMap.ker_le_ker_comp M B

#print axioms kernel_comp_eq_iff_injective_on_range

end D5.S3.Observer.LinearMemory.LosslessLinearPostprocessing

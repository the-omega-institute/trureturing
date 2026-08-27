/- GID: D5/S3/Observer/LinearMemory/ReflectionUnitMemoryResidual
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/ReflectionUnitMemoryResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reflection adds the current kernel modulo its maximal invariant core. -/

import D5.S3.Observer.LinearMemory.ZeroMemoryCriterion

/- Library-search audit trail (2026-08-27):
   * Exact repository hits `eventualKernel`, `eventualKernel_le_ker`,
     `eventualKernel_invariant`, `eventualKernel_is_greatest`, and
     `memoryQuotient` supply the canonical linear reflection objects.
   * Exact pinned-Mathlib hit `Submodule.Quotient.mk_eq_zero` supplies the
     computation rule for the canonical quotient map.
   * No single frozen theorem packages the unit inclusion, maximal invariant
     core, and quotient residual clauses of the source corollary. -/

namespace D5.S3.Observer.LinearMemory.ReflectionUnitMemoryResidual

open D5.S3.Observer.LinearMemory.ZeroMemoryCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The all-future kernel is the maximal update-invariant part of the current
kernel, and the canonical map to the memory quotient kills exactly that part. -/
theorem reflection_unit_memory_residual
    {K V W : Type*} [Ring K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (C : V →ₗ[K] W) (T : V →ₗ[K] V) :
    eventualKernel C T ≤ LinearMap.ker C ∧
      (∀ x ∈ eventualKernel C T, T x ∈ eventualKernel C T) ∧
      (∀ M : Submodule K V,
        M ≤ LinearMap.ker C →
          (∀ x ∈ M, T x ∈ M) → M ≤ eventualKernel C T) ∧
      ∀ x : LinearMap.ker C,
        (Submodule.Quotient.mk x : memoryQuotient C T) = 0 ↔
          (x : V) ∈ eventualKernel C T := by
  refine ⟨eventualKernel_le_ker C T, eventualKernel_invariant C T, ?_, ?_⟩
  · intro M hkernel hinvariant
    exact eventualKernel_is_greatest C T M ⟨hkernel, hinvariant⟩
  · intro x
    rw [Submodule.Quotient.mk_eq_zero]
    rfl

#print axioms reflection_unit_memory_residual

end D5.S3.Observer.LinearMemory.ReflectionUnitMemoryResidual

/- GID: D5/S3/Observer/LinearMemory/MemoryDimensionFormula
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/MemoryDimensionFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Memory quotient dimension equals future-observable dimension minus current rank. -/

import D5.S3.Observer.LinearMemory.ZeroMemoryCriterion
import D5.S3.ObserverMemory.Dynamics.InfiniteObservabilityOrthogonalDuality

/- Library-search audit trail (2026-08-27):
   * `ZeroMemoryCriterion` supplies the canonical `eventualKernel`, its inclusion
     in the current kernel, and the canonical `memoryQuotient`.
   * `InfiniteObservabilityOrthogonalDuality` identifies the all-future kernel
     with the orthogonal complement of the source's adjoint-observable span.
   * Repository body-shape searches found no existing theorem stating this
     dimension identity. Exact Mathlib components `Submodule.finrank_quotient`,
     `Submodule.comapSubtypeEquivOfLe`, `LinearMap.finrank_range_add_finrank_ker`,
     and `Submodule.finrank_add_finrank_orthogonal` are applied directly. -/

noncomputable section

open scoped InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.LinearMemory.MemoryDimensionFormula

open D5.S3.Observer.LinearMemory.ZeroMemoryCriterion
open D5.S3.ObserverMemory.Dynamics.InfiniteObservabilityOrthogonalDuality

local instance memoryQuotientAddCommGroup
    {K V W : Type*} [Ring K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (C : V →ₗ[K] W) (T : V →ₗ[K] V) :
    AddCommGroup (memoryQuotient C T) :=
  inferInstanceAs (AddCommGroup
    ((LinearMap.ker C) ⧸
      (eventualKernel C T).comap (LinearMap.ker C).subtype))

local instance memoryQuotientModule
    {K V W : Type*} [Ring K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (C : V →ₗ[K] W) (T : V →ₗ[K] V) :
    Module K (memoryQuotient C T) :=
  inferInstanceAs (Module K
    ((LinearMap.ker C) ⧸
      (eventualKernel C T).comap (LinearMap.ker C).subtype))

/-- In finite dimension, the canonical memory quotient has dimension equal to
the all-future observable dimension minus the rank of the current readout. -/
theorem memory_dimension_formula
    {𝕜 V Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y]
    (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) :
    Module.finrank 𝕜 (memoryQuotient C T) =
      Module.finrank 𝕜
          (Submodule.span 𝕜
            {v | ∃ k : ℕ, ∃ y : Y,
              v = (T.adjoint ^ k) (C.adjoint y)}) -
        Module.finrank 𝕜 C.range := by
  let observable : Submodule 𝕜 V :=
    Submodule.span 𝕜
      {v | ∃ k : ℕ, ∃ y : Y,
        v = (T.adjoint ^ k) (C.adjoint y)}
  have eventualAsIntersection :
      eventualKernel C T =
        ⨅ k : ℕ, LinearMap.ker (C.comp (T ^ k)) := by
    ext x
    rw [Submodule.mem_iInf]
    change
      (∀ k : ℕ, (T^[k]) x ∈ LinearMap.ker C) ↔
        ∀ k : ℕ, x ∈ LinearMap.ker (C.comp (T ^ k))
    constructor
    · intro hx k
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Module.End.pow_apply]
      exact (LinearMap.mem_ker).mp (hx k)
    · intro hx k
      rw [LinearMap.mem_ker]
      have hk := hx k
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Module.End.pow_apply] at hk
      exact hk
  have eventualAsOrthogonal : eventualKernel C T = observableᗮ := by
    rw [eventualAsIntersection]
    simpa only [observable] using
      infinite_unobservable_eq_observable_orthogonal T C
  have comapFinrank :
      Module.finrank 𝕜
          ((eventualKernel C T).comap (LinearMap.ker C).subtype) =
        Module.finrank 𝕜 (eventualKernel C T) :=
    (Submodule.comapSubtypeEquivOfLe
      (eventualKernel_le_ker C T)).finrank_eq
  have rankNullity := C.finrank_range_add_finrank_ker
  have orthogonalSplit := observable.finrank_add_finrank_orthogonal
  change
    Module.finrank 𝕜
        ((LinearMap.ker C) ⧸
          (eventualKernel C T).comap (LinearMap.ker C).subtype) =
      Module.finrank 𝕜 observable - Module.finrank 𝕜 C.range
  rw [Submodule.finrank_quotient, comapFinrank, eventualAsOrthogonal]
  omega

#print axioms memory_dimension_formula

end D5.S3.Observer.LinearMemory.MemoryDimensionFormula

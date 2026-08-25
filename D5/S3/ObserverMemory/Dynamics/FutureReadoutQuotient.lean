/- GID: D5/S3/ObserverMemory/Dynamics/FutureReadoutQuotient
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Dynamics/FutureReadoutQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The future-kernel quotient is coarsest and carries unique dynamics. -/

import D5.S3.ObserverMemory.Dynamics.MaximalUnobservableSubspace
import Mathlib.LinearAlgebra.Isomorphisms

/- Library-search audit trail (2026-08-25):
   * Exact family hit `future_kernel_is_maximal_invariant` supplies the source's
     all-future kernel and its update invariance; it is applied directly.
   * The close hit `minimal_predictive_completion_quotient` concerns arbitrary
     set quotients and does not state uniqueness of its induced dynamics, so it
     is not an exact cover of this linear quotient claim.
   * Repository body-shape searches for `liftQ`, `mkQ_surjective`, and
     `quotKerEquivRange` found adjacent quotient proofs but no declaration with
     all three public clauses below.
   * Exact pinned-Mathlib hits `Submodule.liftQ`, `Submodule.mkQ_surjective`,
     and `LinearMap.quotKerEquivRange` provide the canonical descents and the
     unique factor through the effective range of any sufficient summary. -/

namespace D5.S3.ObserverMemory.Dynamics.FutureReadoutQuotient

open D5.S3.ObserverMemory.Dynamics.MaximalUnobservableSubspace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The quotient by the intersection of all future readout kernels preserves
every future readout and is coarsest among linear quotients with that property.
The source evolution also descends to it in exactly one way. -/
theorem future_readout_quotient_is_coarsest_with_unique_dynamics
    {𝕜 V Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y]
    (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) :
    let hidden := ⨅ k : ℕ, LinearMap.ker (C.comp (T ^ k))
    (∃ readout : ℕ → (V ⧸ hidden) →ₗ[𝕜] Y,
      ∀ k x, readout k (hidden.mkQ x) = C ((T ^ k) x)) ∧
    (∀ (Q : Type*) [AddCommGroup Q] [Module 𝕜 Q]
        (summary : V →ₗ[𝕜] Q),
      (∀ x y, summary x = summary y →
        ∀ k, C ((T ^ k) x) = C ((T ^ k) y)) →
      ∃! factor : LinearMap.range summary →ₗ[𝕜] (V ⧸ hidden),
        hidden.mkQ = factor.comp summary.rangeRestrict) ∧
    ∃! induced : (V ⧸ hidden) →ₗ[𝕜] (V ⧸ hidden),
      ∀ x, induced (hidden.mkQ x) = hidden.mkQ (T x) := by
  dsimp only
  let hidden : Submodule 𝕜 V :=
    ⨅ k : ℕ, LinearMap.ker (C.comp (T ^ k))
  have hiddenInvariant : Set.MapsTo T hidden hidden := by
    simpa [hidden] using
      (future_kernel_is_maximal_invariant T C).2.1
  refine ⟨?_, ?_, ?_⟩
  · let readout : ℕ → (V ⧸ hidden) →ₗ[𝕜] Y := fun k =>
      hidden.liftQ (C.comp (T ^ k)) (by
        simpa [hidden] using
          (iInf_le (fun n : ℕ => LinearMap.ker (C.comp (T ^ n))) k))
    refine ⟨readout, ?_⟩
    intro k x
    rfl
  · intro Q _ _ summary determinesFuture
    have summaryKernelHidden : summary.ker ≤ hidden := by
      intro x hx
      apply (Submodule.mem_iInf _).mpr
      intro k
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      have sameSummary : summary x = summary 0 := by
        simpa [LinearMap.mem_ker] using hx
      simpa using determinesFuture x 0 sameSummary k
    have summaryKernelProjection : summary.ker ≤ LinearMap.ker hidden.mkQ := by
      intro x hx
      rw [LinearMap.mem_ker]
      exact (Submodule.Quotient.mk_eq_zero hidden).mpr
        (summaryKernelHidden hx)
    let factor : LinearMap.range summary →ₗ[𝕜] (V ⧸ hidden) :=
      (summary.ker.liftQ hidden.mkQ summaryKernelProjection).comp
        summary.quotKerEquivRange.symm.toLinearMap
    have factorizes :
        hidden.mkQ = factor.comp summary.rangeRestrict := by
      apply LinearMap.ext
      intro x
      change hidden.mkQ x =
        (summary.ker.liftQ hidden.mkQ summaryKernelProjection)
          (summary.quotKerEquivRange.symm
            ⟨summary x, summary.mem_range_self x⟩)
      rw [LinearMap.quotKerEquivRange_symm_apply_image]
      rfl
    refine ⟨factor, factorizes, ?_⟩
    intro other hother
    apply LinearMap.ext
    intro value
    obtain ⟨x, hx⟩ := value.property
    have value_eq : value = ⟨summary x, summary.mem_range_self x⟩ :=
      Subtype.ext hx.symm
    rw [value_eq]
    have otherAt := LinearMap.congr_fun hother x
    have factorAt := LinearMap.congr_fun factorizes x
    exact otherAt.symm.trans factorAt
  · have hiddenKernelProjection : hidden ≤ LinearMap.ker (hidden.mkQ.comp T) := by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact (Submodule.Quotient.mk_eq_zero hidden).mpr
        (hiddenInvariant hx)
    let induced : (V ⧸ hidden) →ₗ[𝕜] (V ⧸ hidden) :=
      hidden.liftQ (hidden.mkQ.comp T) hiddenKernelProjection
    have inducedCommutes :
        ∀ x, induced (hidden.mkQ x) = hidden.mkQ (T x) := by
      intro x
      rfl
    refine ⟨induced, inducedCommutes, ?_⟩
    intro other hother
    apply LinearMap.ext
    intro quotientState
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective hidden quotientState
    exact (hother x).trans (inducedCommutes x).symm

#print axioms future_readout_quotient_is_coarsest_with_unique_dynamics

end D5.S3.ObserverMemory.Dynamics.FutureReadoutQuotient

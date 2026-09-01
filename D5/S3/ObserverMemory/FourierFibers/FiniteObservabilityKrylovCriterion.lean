/- GID: D5/S3/ObserverMemory/FourierFibers/FiniteObservabilityKrylovCriterion
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/FiniteObservabilityKrylovCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite time window is faithful exactly when its existing
     observable Krylov space fills the carrier. -/

import D5.S3.ObserverMemory.Dynamics.FiniteObservabilityOrthogonalDuality

/-!
Library-first note: the repository already proves that the finite hidden kernel
is the orthogonal complement of `observableKrylov`.  This owner adds only the
faithfulness criterion obtained by combining that theorem with Mathlib's
finite-dimensional orthogonal-complement characterization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.FiniteObservabilityKrylovCriterion

open scoped InnerProductSpace

open D5.S3.ObserverMemory.Dynamics.FiniteObservabilityOrthogonalDuality
open D5.S3.ObserverMemory.Dynamics.ObservableKrylovGrowthBound

/-- Trivial finite unobservable kernel is equivalent to the finite observable
Krylov space spanning the full carrier. -/
theorem finite_hidden_kernel_trivial_iff_observable_krylov_top
    {𝕜 V Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y]
    (evolution : V →ₗ[𝕜] V) (readout : V →ₗ[𝕜] Y) (depth : ℕ) :
    (⨅ time : Set.Iic depth,
        LinearMap.ker (readout.comp (evolution ^ (time : ℕ)))) = ⊥ ↔
      observableKrylov evolution readout depth = ⊤ := by
  rw [finite_unobservable_eq_observable_orthogonal]
  exact Submodule.orthogonal_eq_bot_iff

/-- Failure of full observable span is exactly the existence of a nontrivial
finite hidden subspace. -/
theorem finite_hidden_kernel_nontrivial_iff_observable_krylov_ne_top
    {𝕜 V Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y]
    (evolution : V →ₗ[𝕜] V) (readout : V →ₗ[𝕜] Y) (depth : ℕ) :
    (⨅ time : Set.Iic depth,
        LinearMap.ker (readout.comp (evolution ^ (time : ℕ)))) ≠ ⊥ ↔
      observableKrylov evolution readout depth ≠ ⊤ := by
  exact not_congr
    (finite_hidden_kernel_trivial_iff_observable_krylov_top
      evolution readout depth)

#print axioms finite_hidden_kernel_trivial_iff_observable_krylov_top
#print axioms finite_hidden_kernel_nontrivial_iff_observable_krylov_ne_top

end D5.S3.ObserverMemory.FourierFibers.FiniteObservabilityKrylovCriterion

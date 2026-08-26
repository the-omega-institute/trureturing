/- GID: D5/S3/ObserverMemory/Dynamics/FiniteObservabilityOrthogonalDuality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Dynamics/FiniteObservabilityOrthogonalDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Each finite readout kernel is the orthogonal complement of its observable Krylov space. -/

import D5.S3.ObserverMemory.Dynamics.InfiniteObservabilityOrthogonalDuality

/- Library-search audit trail (2026-08-25):
   * Repository searches found the exact canonical finite visible-space
     construction `observableKrylov`, which is imported and instantiated here.
     No existing D5 theorem equates its orthogonal complement with the finite
     intersection of readout kernels.
   * Pinned Mathlib has no theorem packaging the complete finite-depth
     equality. Exact component hits `LinearMap.adjoint_inner_right` and
     `Submodule.mem_orthogonal'` are applied directly below.
   * The hidden object is constructed publicly from the source test
     `C.comp (T ^ k)` over the exact index subtype `k <= m`; no new definition
     or target-shaped abbreviation is introduced. -/

namespace D5.S3.ObserverMemory.Dynamics.FiniteObservabilityOrthogonalDuality

open scoped InnerProductSpace

open D5.S3.ObserverMemory.Dynamics.ObservableKrylovGrowthBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- At every finite depth, the states annihilated by all readouts through that
depth are exactly the vectors orthogonal to the observable Krylov space. -/
theorem finite_unobservable_eq_observable_orthogonal
    {𝕜 V Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y]
    (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) (m : ℕ) :
    (⨅ k : Set.Iic m, LinearMap.ker (C.comp (T ^ (k : ℕ)))) =
      (observableKrylov T C m)ᗮ := by
  have hadjointPower (k : ℕ) : (T ^ k).adjoint = T.adjoint ^ k := by
    change star (T ^ k) = star T ^ k
    exact star_pow T k
  ext x
  rw [Submodule.mem_iInf, Submodule.mem_orthogonal', observableKrylov]
  constructor
  · intro hx v hv
    refine Submodule.span_induction
      (p := fun (v : V) _ => inner 𝕜 x v = 0)
      ?_ ?_ ?_ ?_ hv
    · intro v hv
      rcases hv with ⟨k, hk, y, rfl⟩
      have hkernel := hx ⟨k, hk⟩
      rw [LinearMap.mem_ker] at hkernel
      have hreadout : C ((T ^ k) x) = 0 := by
        simpa only [LinearMap.comp_apply] using hkernel
      calc
        ⟪x, (T.adjoint ^ k) (C.adjoint y)⟫_𝕜 =
            ⟪(T ^ k) x, C.adjoint y⟫_𝕜 := by
              simpa only [hadjointPower k] using
                (LinearMap.adjoint_inner_right (T ^ k) x (C.adjoint y))
        _ = ⟪C ((T ^ k) x), y⟫_𝕜 :=
          LinearMap.adjoint_inner_right C ((T ^ k) x) y
        _ = 0 := by simp only [hreadout, inner_zero_left]
    · simp
    · intro u v _ _ hu hv
      simp only [inner_add_right, hu, hv, add_zero]
    · intro a v _ hv
      simp only [inner_smul_right, hv, mul_zero]
  · intro hx k
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    apply ext_inner_right 𝕜
    intro y
    have horthogonal := hx
      ((T.adjoint ^ (k : ℕ)) (C.adjoint y))
      (Submodule.subset_span ⟨k, k.property, y, rfl⟩)
    calc
      ⟪C ((T ^ (k : ℕ)) x), y⟫_𝕜 =
          ⟪(T ^ (k : ℕ)) x, C.adjoint y⟫_𝕜 :=
        (LinearMap.adjoint_inner_right C ((T ^ (k : ℕ)) x) y).symm
      _ = ⟪x, (T.adjoint ^ (k : ℕ)) (C.adjoint y)⟫_𝕜 := by
        simpa only [hadjointPower (k : ℕ)] using
          (LinearMap.adjoint_inner_right
            (T ^ (k : ℕ)) x (C.adjoint y)).symm
      _ = 0 := horthogonal
      _ = ⟪(0 : Y), y⟫_𝕜 := by simp

#print axioms finite_unobservable_eq_observable_orthogonal

end D5.S3.ObserverMemory.Dynamics.FiniteObservabilityOrthogonalDuality

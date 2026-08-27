/- GID: D5/S3/Observer/Linear/LeastSquaresReconstructionNoiseBound
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/LeastSquaresReconstructionNoiseBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Full-rank least-squares reconstruction has a sharp linear noise bound. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Real.Sqrt

/- Library-search audit trail (2026-08-27):
   * D5 searches found `RobustFrameBounds.robust_observer_frame_bounds`, which
     supplies the adjacent spectral frame interpretation, but no exact theorem
     coupling a noisy observation model to least-squares reconstruction error.
   * Pinned Mathlib has no Moore--Penrose construction; its
     `LinearAlgebra/Matrix/NonsingularInverse.lean` explicitly says that
     pseudoinverses are not considered. The public least-squares clause is
     therefore stated by its exact full-column-rank normal equation.
   * Exact Mathlib hits `LinearMap.adjoint_inner_right`,
     `real_inner_self_eq_norm_sq`, `real_inner_le_norm`, `sq_le_sq₀`, and
     `Real.sq_sqrt` supply the proof without redeclaring an inverse.
   * Body-shape searches found no D5 observation-model or reconstruction-error
     primitive with this signature. This module introduces no `def` or `abbrev`;
     every source object remains a public theorem argument. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Linear.LeastSquaresReconstructionNoiseBound

open InnerProductSpace
open scoped RealInnerProductSpace

/-- A positive lower frame bound and the least-squares normal equation give the
sharp `1 / sqrt alpha` reconstruction-noise factor. The normal equation is the
Moore--Penrose least-squares characterization available without introducing a
noncanonical pseudoinverse into the repository. -/
theorem least_squares_reconstruction_noise_bound
    {State Observation : Type*}
    [NormedAddCommGroup State] [InnerProductSpace ℝ State]
    [FiniteDimensional ℝ State]
    [NormedAddCommGroup Observation] [InnerProductSpace ℝ Observation]
    [FiniteDimensional ℝ Observation]
    (measurement : State →ₗ[ℝ] Observation)
    (alpha : ℝ) (alphaPositive : 0 < alpha)
    (lowerFrame : ∀ difference : State,
      alpha * ‖difference‖ ^ 2 ≤ ‖measurement difference‖ ^ 2)
    (trueState reconstructed : State) (data noise : Observation)
    (observationModel : data = measurement trueState + noise)
    (leastSquaresNormal :
      LinearMap.adjoint measurement (measurement reconstructed - data) = 0) :
    ‖reconstructed - trueState‖ ≤ ‖noise‖ / Real.sqrt alpha := by
  let error := reconstructed - trueState
  have residualIdentity :
      measurement reconstructed - data = measurement error - noise := by
    simp [error, observationModel, sub_add_eq_sub_sub]
  have errorNormal :
      LinearMap.adjoint measurement (measurement error - noise) = 0 := by
    rw [← residualIdentity]
    exact leastSquaresNormal
  have orthogonality :
      inner ℝ (measurement error) (measurement error - noise) = 0 := by
    calc
      inner ℝ (measurement error) (measurement error - noise) =
          inner ℝ error
            (LinearMap.adjoint measurement (measurement error - noise)) := by
        exact (measurement.adjoint_inner_right error
          (measurement error - noise)).symm
      _ = 0 := by rw [errorNormal]; simp
  have energyIdentity :
      ‖measurement error‖ ^ 2 = inner ℝ (measurement error) noise := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq] at orthogonality
    linarith
  have energyLe :
      ‖measurement error‖ ^ 2 ≤ ‖measurement error‖ * ‖noise‖ := by
    rw [energyIdentity]
    exact real_inner_le_norm (measurement error) noise
  have measuredErrorLe : ‖measurement error‖ ≤ ‖noise‖ := by
    by_cases measuredZero : ‖measurement error‖ = 0
    · simp [measuredZero]
    · have measuredPositive : 0 < ‖measurement error‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm measuredZero)
      nlinarith
  have lowerLinear :
      Real.sqrt alpha * ‖error‖ ≤ ‖measurement error‖ := by
    rw [← sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      (norm_nonneg _), mul_pow, Real.sq_sqrt alphaPositive.le]
    exact lowerFrame error
  change ‖error‖ ≤ ‖noise‖ / Real.sqrt alpha
  rw [le_div_iff₀ (Real.sqrt_pos.2 alphaPositive)]
  simpa [mul_comm] using lowerLinear.trans measuredErrorLe

#print axioms least_squares_reconstruction_noise_bound

end D5.S3.Observer.Linear.LeastSquaresReconstructionNoiseBound

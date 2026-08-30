/- GID: D5/S3/Observer/Conditioning/TargetVisibilityMinimumVariance
   generality: G
   mirror-B: D5/B/S3/Observer/Conditioning/TargetVisibilityMinimumVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Isotropic noise makes the canonical visible coefficient minimum-variance at zero too. -/

import D5.S3.Observer.Conditioning.TargetVisibilityConditionCost

/- Library-search audit trail (2026-08-30):
   * Six repository searches found only the imported minimum-norm target certificate; no Lean or
     Blueprint declaration states its isotropic-covariance minimum-variance consequence.
   * Loogle found `sq_le_sq₀` and `mul_le_mul_of_nonneg_left` for the required order shape.
   * LeanSearch returned no response for the minimum-variance unbiased-estimator query.
   * Pinned Mathlib has covariance bilinear/operator APIs but no Gauss--Markov or BLUE theorem.
     The covariance operator is therefore an explicit input, without a second pseudoinverse. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Conditioning.TargetVisibilityMinimumVariance

open InnerProductSpace

/-- The scalar variance induced by a covariance operator on an observation coefficient. -/
noncomputable def estimatorVariance
    {K Observation : Type*}
    [RCLike K]
    [NormedAddCommGroup Observation] [InnerProductSpace K Observation]
    (covariance : Observation →ₗ[K] Observation) (coefficient : Observation) : ℝ :=
  RCLike.re (inner K coefficient (covariance coefficient))

/-- A covariance operator is isotropic with scale `noiseScale` when it is `noiseScale ^ 2` times
the identity. The square permits the degenerate zero-noise case without a sign assumption. -/
def IsIsotropicCovariance
    {K Observation : Type*}
    [RCLike K]
    [NormedAddCommGroup Observation] [InnerProductSpace K Observation]
    (covariance : Observation →ₗ[K] Observation) (noiseScale : ℝ) : Prop :=
  covariance = ((noiseScale ^ 2 : ℝ) : K) •
    (LinearMap.id : Observation →ₗ[K] Observation)

/-- A canonical state/coefficient pair is a minimum-variance target certificate when it lies in
the visible Gram slice, is unbiased, minimizes covariance variance, and has the stated cost. -/
def IsMinimumVarianceCertificate
    {K State Observation : Type*}
    [RCLike K]
    [NormedAddCommGroup State] [InnerProductSpace K State]
    [FiniteDimensional K State]
    [NormedAddCommGroup Observation] [InnerProductSpace K Observation]
    [FiniteDimensional K Observation]
    (measurement : State →ₗ[K] Observation) (target : State)
    (covariance : Observation →ₗ[K] Observation) (noiseScale : ℝ)
    (certificate : State × Observation) : Prop :=
  certificate.1 ∈ measurement.kerᗮ ∧
    measurement.adjoint certificate.2 = target ∧
    certificate.2 = measurement certificate.1 ∧
    (∀ coefficient : Observation,
      measurement.adjoint coefficient = target →
        estimatorVariance covariance certificate.2 ≤
          estimatorVariance covariance coefficient) ∧
    estimatorVariance covariance certificate.2 =
      noiseScale ^ 2 * RCLike.re (inner K target certificate.1)

private theorem estimatorVariance_of_isotropic
    {K Observation : Type*}
    [RCLike K]
    [NormedAddCommGroup Observation] [InnerProductSpace K Observation]
    (covariance : Observation →ₗ[K] Observation) (noiseScale : ℝ)
    (isotropic : IsIsotropicCovariance covariance noiseScale)
    (coefficient : Observation) :
    estimatorVariance covariance coefficient = noiseScale ^ 2 * ‖coefficient‖ ^ 2 := by
  rw [isotropic]
  simp [estimatorVariance, inner_smul_right, inner_self_eq_norm_sq_to_K]

/-- Exact target visibility gives a canonical unbiased coefficient whose variance is minimal under
isotropic observation covariance and equals the noise scale times the target condition cost. -/
theorem target_visibility_minimum_variance
    {K State Observation : Type*}
    [RCLike K]
    [NormedAddCommGroup State] [InnerProductSpace K State]
    [FiniteDimensional K State]
    [NormedAddCommGroup Observation] [InnerProductSpace K Observation]
    [FiniteDimensional K Observation]
    (measurement : State →ₗ[K] Observation) (target : State)
    (covariance : Observation →ₗ[K] Observation) (noiseScale : ℝ)
    (isotropic : IsIsotropicCovariance covariance noiseScale)
    (visible : ∀ x y : State, measurement x = measurement y →
      inner K target x = inner K target y) :
    ∃ certificate : State × Observation,
      IsMinimumVarianceCertificate measurement target covariance noiseScale certificate := by
  rcases
      (TargetVisibilityConditionCost.target_visibility_condition_cost measurement target).mp
        visible with
    ⟨certificate, certificateProperties, _⟩
  rcases certificateProperties with
    ⟨stateOrthogonal, coefficientNormal, coefficientFromState, coefficientMinimal,
      conditionCost⟩
  refine ⟨certificate, stateOrthogonal, coefficientNormal, coefficientFromState, ?_, ?_⟩
  · intro coefficient candidateNormal
    rw [estimatorVariance_of_isotropic covariance noiseScale isotropic,
      estimatorVariance_of_isotropic covariance noiseScale isotropic]
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
        (coefficientMinimal coefficient candidateNormal))
      (sq_nonneg noiseScale)
  · rw [estimatorVariance_of_isotropic covariance noiseScale isotropic]
    congr 1
    simpa using congrArg RCLike.re conditionCost

#print axioms target_visibility_minimum_variance

/-- Without target visibility, the zero measurement on `ℝ` has no unbiased coefficient for the
nonzero target, so no minimum-variance certificate can exist. -/
theorem target_visibility_is_necessary :
    (¬ ∀ x y : ℝ, (0 : ℝ →ₗ[ℝ] ℝ) x = (0 : ℝ →ₗ[ℝ] ℝ) y →
      inner ℝ 1 x = inner ℝ 1 y) ∧
    IsIsotropicCovariance (0 : ℝ →ₗ[ℝ] ℝ) 0 ∧
    ¬ ∃ certificate : ℝ × ℝ,
      IsMinimumVarianceCertificate (0 : ℝ →ₗ[ℝ] ℝ) 1 0 0 certificate := by
  constructor
  · push Not
    exact ⟨0, 1, by simp, by norm_num⟩
  · simp [IsIsotropicCovariance, IsMinimumVarianceCertificate]

#print axioms target_visibility_is_necessary

/-- Without isotropy, correlated two-coordinate noise makes a noncanonical unbiased coefficient
strictly less variable than the canonical minimum-norm coefficient. -/
theorem isotropic_covariance_is_necessary :
    let first : EuclideanSpace ℝ (Fin 2) := !₂[1, 0]
    let correlated : EuclideanSpace ℝ (Fin 2) := !₂[1, 1]
    let measurement : ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      LinearMap.toSpanSingleton ℝ _ first
    let covariance : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      (rankOne ℝ correlated correlated).toLinearMap
    (∀ x y : ℝ, measurement x = measurement y → inner ℝ 1 x = inner ℝ 1 y) ∧
    ¬ IsIsotropicCovariance covariance 1 ∧
    ¬ IsMinimumVarianceCertificate measurement 1 covariance 1 (1, first) := by
  dsimp
  constructor
  · intro x y equalMeasurements
    have equalFirstCoordinates := congrArg (fun z => z 0) equalMeasurements
    simpa using equalFirstCoordinates
  · constructor
    · intro isotropic
      have equalAtFirst := congrArg
        (fun operator : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) =>
          operator !₂[1, 0]) isotropic
      have equalSecondCoordinates := congrArg (fun z => z 1) equalAtFirst
      norm_num [IsIsotropicCovariance, rankOne_apply, PiLp.inner_apply,
        Fin.sum_univ_two] at equalSecondCoordinates
    · rintro ⟨_, _, _, minimumVariance, _⟩
      have competingNormal :
          (LinearMap.toSpanSingleton ℝ (EuclideanSpace ℝ (Fin 2)) !₂[1, 0]).adjoint
              !₂[1, -1] = 1 := by
        simp [LinearMap.adjoint_toSpanSingleton, PiLp.inner_apply, Fin.sum_univ_two]
      have varianceOrder := minimumVariance !₂[1, -1] competingNormal
      norm_num [estimatorVariance, rankOne_apply, PiLp.inner_apply,
        Fin.sum_univ_two] at varianceOrder

#print axioms isotropic_covariance_is_necessary

/-- Degenerate inputs remain valid: zero measurement at zero scale has a certificate, as does the
identity measurement on the singleton zero-dimensional Euclidean space. -/
theorem degenerate_inputs_have_witnesses :
    (∃ certificate : ℝ × ℝ,
      IsMinimumVarianceCertificate (0 : ℝ →ₗ[ℝ] ℝ) 0 0 0 certificate) ∧
    (∃ certificate :
      EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 0),
      IsMinimumVarianceCertificate
        (LinearMap.id : EuclideanSpace ℝ (Fin 0) →ₗ[ℝ] EuclideanSpace ℝ (Fin 0))
        0 0 0 certificate) := by
  constructor
  · apply target_visibility_minimum_variance
    · simp [IsIsotropicCovariance]
    · simp
  · apply target_visibility_minimum_variance
    · simp [IsIsotropicCovariance]
    · simp

#print axioms degenerate_inputs_have_witnesses

end D5.S3.Observer.Conditioning.TargetVisibilityMinimumVariance

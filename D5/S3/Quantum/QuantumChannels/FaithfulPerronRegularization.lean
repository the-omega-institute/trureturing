/- GID: D5/S3/Quantum/QuantumChannels/FaithfulPerronRegularization
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FaithfulPerronRegularization
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Positive regularization produces faithful Perron eigenmatrices. -/

/- Judgement:
   admission_basis: escape-witness.
   Module escape_witness: D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.strict_positive_perron_eigenmatrix.
   Direct frozen dependencies:
   D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity: statement_id sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988.
   D5/S3/Quantum/Fibers/PhysicalFiber.finite_dimensional_physical_fiber: statement_id sha256:20c3cc4b8eb976ba90fe5823cc1a6fb4ef0812d411aa5a82926a53aa578aa013.
   Information-escape registration is paused under CLAUDE.md §3.9.
   D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.Regularized: proof_shape: not-applicable; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.RegularizedPerronGoal, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.epsilon_route_conditional, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.regularized_tendsto, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.twoPositive_spectralBound.
   D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.PerronCertificate: proof_shape: not-applicable; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.RegularizedPerronGoal, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.UnitalSimilarityGoal, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.epsilon_rescaling_is_algebraic.
   D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.RegularizedPerronGoal: proof_shape: not-applicable; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.regularized_perron_certificate, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.epsilon_route_conditional.
   _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.density_isClosed: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.feasible_isClosed.
   _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.feasibleSet: proof_shape: not-applicable; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.feasible_isClosed, _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.collatz_minimum_exists, _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.positive_has_feasible_constant, _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.strict_positive_feasible_faithful, D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.strict_positive_perron_eigenmatrix.
   _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.feasible_isClosed: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.collatz_minimum_exists.
   _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.collatz_minimum_exists: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.strict_positive_perron_eigenmatrix.
   _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.positive_has_feasible_constant: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.strict_positive_perron_eigenmatrix.
   _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.collatz_residual_identity: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.collatz_residual_strict.
   _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.collatz_residual_strict: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.strict_positive_perron_eigenmatrix.
   _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.positive_definite_residual_lowering: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.strict_positive_perron_eigenmatrix.
   _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.strict_positive_feasible_faithful: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.strict_positive_perron_eigenmatrix.
   D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.strict_positive_perron_eigenmatrix: proof_shape: content; escape_witness: D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.strict_positive_perron_eigenmatrix; consumer: _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.regularized_perron_and_max_real.
   _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.faithful_perron_eigenvalue_bound: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.matrix_faithful_perron_bound.
   _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.matrix_faithful_perron_bound: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.faithful_perron_max_real, D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.regularized_perron_certificate.
   _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.faithful_perron_max_real: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.regularized_perron_and_max_real.
   _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.regularized_perron_and_max_real: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.regularized_perron_certificate.
   _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.spectralRadius_eq_of_root_bounds: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.regularized_perron_certificate.
   D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.regularized_perron_certificate: proof_shape: content; escape_witness: D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.strict_positive_perron_eigenmatrix; consumer: _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.twoPositive_spectralBound.
-/
import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
import D5.S3.Quantum.Fibers.PhysicalFiber
import D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
noncomputable section
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology ENNReal NNReal
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity
open D5.S3.Quantum.Fibers.PhysicalFiber
open D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
namespace D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization
variable {d : ℕ}
section
variable {d : ℕ}
def Regularized {d : ℕ} (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (ε : ℝ) : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) :=
  T + (ε : ℂ) • ((Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight
    (1 : Matrix (Fin d) (Fin d) ℂ))
structure PerronCertificate {d : ℕ} (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) where
  rho : (Matrix (Fin d) (Fin d) ℂ)
  c : ℝ
  rho_pos : rho.PosDef
  rho_trace : Matrix.trace rho = 1
  eigen : T rho = (c : ℂ) • rho
  c_pos : 0 < c
  c_is_max : c = maxReSpectrum T
  c_is_radius : spectralRadius ℂ T.toContinuousLinearMap = ENNReal.ofReal c
def RegularizedPerronGoal : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (ε : ℝ), 0 < ε →
    (KPositive 2 _ T) → Nonempty (PerronCertificate (Regularized T ε))
end
section
variable {d : ℕ}
private lemma density_isClosed (d : ℕ) : IsClosed ({ρ : Matrix (Fin d) (Fin d) ℂ | D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity ρ}) := by
  have hpos : IsClosed {ρ : (Matrix (Fin d) (Fin d) ℂ) | ρ.PosSemidef} := by
    simpa only [Set.Ici, Set.mem_setOf_eq, Set.preimage_setOf_eq, ← Matrix.nonneg_iff_posSemidef] using
      (isClosed_Ici : IsClosed (Ici (0 : (Matrix (Fin d) (Fin d) ℂ))))
  have htrace : IsClosed {ρ : (Matrix (Fin d) (Fin d) ℂ) | Matrix.trace ρ = 1} := by
    exact isClosed_eq (LinearMap.continuous_of_finiteDimensional
      (Matrix.traceLinearMap (Fin d) ℂ ℂ)) continuous_const
  exact hpos.inter htrace
private def feasibleSet {d : ℕ} (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (C : ℝ) : Set ((Matrix (Fin d) (Fin d) ℂ) × ℝ) :=
  {x | x.1 ∈ {ρ : Matrix (Fin d) (Fin d) ℂ | D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity ρ} ∧ x.2 ∈ Icc 0 C ∧
    (((x.2 : ℂ) • x.1) - T x.1).PosSemidef}
private lemma feasible_isClosed {d : ℕ} (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (C : ℝ) :
    IsClosed (feasibleSet T C) := by
  have hstate : IsClosed {x : (Matrix (Fin d) (Fin d) ℂ) × ℝ | x.1 ∈ {ρ : Matrix (Fin d) (Fin d) ℂ | D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity ρ}} :=
    (density_isClosed d).preimage continuous_fst
  have hc : IsClosed {x : (Matrix (Fin d) (Fin d) ℂ) × ℝ | x.2 ∈ Icc 0 C} :=
    isClosed_Icc.preimage continuous_snd
  have hmap : Continuous (fun x : (Matrix (Fin d) (Fin d) ℂ) × ℝ => (x.2 : ℂ) • x.1 - T x.1) := by
    have hT : Continuous T := T.continuous_of_finiteDimensional
    fun_prop
  have hres : IsClosed {x : (Matrix (Fin d) (Fin d) ℂ) × ℝ | (((x.2 : ℂ) • x.1) - T x.1).PosSemidef} := by
    simpa only [Set.Ici, Set.mem_setOf_eq, Set.preimage_setOf_eq, ← Matrix.nonneg_iff_posSemidef] using
      (isClosed_Ici : IsClosed (Ici (0 : (Matrix (Fin d) (Fin d) ℂ)))).preimage hmap
  exact hstate.inter (hc.inter hres)
private lemma collatz_minimum_exists {d : ℕ} [NeZero d] (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (C : ℝ)
    (hne : (feasibleSet T C).Nonempty) :
    ∃ x ∈ feasibleSet T C, ∀ y ∈ feasibleSet T C, x.2 ≤ y.2 := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hstates := finite_dimensional_physical_fiber
    (0 : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] (Empty → ℂ)) x₀.1 hx₀.1.1 hx₀.1.2
  have hset : physicalFiber
      (0 : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] (Empty → ℂ)) x₀.1 = {ρ : Matrix (Fin d) (Fin d) ℂ | D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity ρ} := by
    ext X
    change (0 = 0 ∧ X.PosSemidef ∧ Matrix.trace X = 1) ↔ (X.PosSemidef ∧ Matrix.trace X = 1)
    simp
  rw [hset] at hstates
  have hc : IsCompact (feasibleSet T C) := by
    apply (hstates.2.1.prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) C))).of_isClosed_subset
      (feasible_isClosed T C)
    intro x hx
    exact ⟨hx.1, hx.2.1⟩
  exact hc.exists_isMinOn ⟨x₀, hx₀⟩ continuous_snd.continuousOn
private lemma positive_has_feasible_constant {d : ℕ} [NeZero d] (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (hPos : ∀ X : (Matrix (Fin d) (Fin d) ℂ), X.PosSemidef → (T X).PosSemidef) :
    ∃ C : ℝ, (feasibleSet T C).Nonempty := by
  letI : CStarAlgebra ((Matrix (Fin d) (Fin d) ℂ)) := { }
  let σ : (Matrix (Fin d) (Fin d) ℂ) := (((d : ℝ)⁻¹ : ℂ) • (1 : (Matrix (Fin d) (Fin d) ℂ)))
  let C : ℝ := (d : ℝ) * ‖T σ‖
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hσ : σ ∈ {ρ : Matrix (Fin d) (Fin d) ℂ | D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity ρ} := by
    change σ.PosSemidef ∧ Matrix.trace σ = 1
    constructor
    · exact Matrix.PosSemidef.one.smul (inv_nonneg.mpr (Nat.cast_nonneg d))
    · simp [σ, Matrix.trace, hd]
  have hbound : T σ ≤ (‖T σ‖ : ℝ) • (1 : (Matrix (Fin d) (Fin d) ℂ)) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (hPos σ hσ.1).isHermitian.isSelfAdjoint.le_algebraMap_norm_self
  have hscalar : (C : ℂ) • σ = (‖T σ‖ : ℝ) • (1 : (Matrix (Fin d) (Fin d) ℂ)) := by
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
    ext i j
    simp only [C, σ, Matrix.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    field_simp
    <;> ring
  refine ⟨C, (σ,C), hσ, ⟨by positivity, le_rfl⟩, ?_⟩
  rw [hscalar]
  exact Matrix.le_iff.mp hbound
private theorem collatz_residual_identity {d : ℕ} (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (ρ : (Matrix (Fin d) (Fin d) ℂ))
    (c : ℂ) (hc : c ≠ 0) :
    c • (ρ + c⁻¹ • T ρ) - T (ρ + c⁻¹ • T ρ) =
      (c • ρ - T ρ) + c⁻¹ • T (c • ρ - T ρ) := by
  simp only [smul_add, smul_smul, LinearMap.map_add, LinearMap.map_smul,
    LinearMap.map_sub, smul_sub]
  rw [mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]
  simp only [one_smul]
  abel
private theorem collatz_residual_strict {d : ℕ} (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (hStrict : ∀ X : (Matrix (Fin d) (Fin d) ℂ), X.PosSemidef → X ≠ 0 → (T X).PosDef)
    (ρ : (Matrix (Fin d) (Fin d) ℂ)) (c : ℝ) (hc : 0 < c)
    (hres : ((c : ℂ) • ρ - T ρ).PosSemidef)
    (hne : (c : ℂ) • ρ - T ρ ≠ 0) :
    (((c : ℂ) • (ρ + ((c : ℂ)⁻¹) • T ρ)) -
      T (ρ + ((c : ℂ)⁻¹) • T ρ)).PosDef := by
  have hident := collatz_residual_identity T ρ (c : ℂ) (by exact_mod_cast ne_of_gt hc)
  rw [hident]
  rw [← Complex.ofReal_inv]
  change ((c : ℂ) • ρ - T ρ + (c⁻¹ : ℝ) • T ((c : ℂ) • ρ - T ρ)).PosDef
  exact Matrix.PosDef.posSemidef_add hres ((hStrict _ hres hne).smul (inv_pos.mpr hc))
private theorem positive_definite_residual_lowering {d : ℕ} [NeZero d]
    (D ρ : (Matrix (Fin d) (Fin d) ℂ)) (hD : D.PosDef) (hρ : ρ.PosSemidef) :
    ∃ η : ℝ, 0 < η ∧ (D - (η : ℂ) • ρ).PosSemidef := by
  letI : CStarAlgebra ((Matrix (Fin d) (Fin d) ℂ)) := { }
  obtain ⟨r, hr, hrD⟩ := (CFC.exists_pos_algebraMap_le_iff
    D hD.isHermitian.isSelfAdjoint).2 (fun z hz => hD.isStrictlyPositive.spectrum_pos hz)
  let η : ℝ := r / (‖ρ‖ + 1)
  have hη : 0 < η := div_pos hr (by positivity)
  have hηr : η * ‖ρ‖ ≤ r := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < ‖ρ‖ + 1)).2
    nlinarith
  have hρbound : ρ ≤ (‖ρ‖ : ℝ) • (1 : (Matrix (Fin d) (Fin d) ℂ)) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      hρ.isHermitian.isSelfAdjoint.le_algebraMap_norm_self
  have hstep : (η : ℝ) • ρ ≤ r • (1 : (Matrix (Fin d) (Fin d) ℂ)) := by
    calc
      η • ρ ≤ η • ((‖ρ‖ : ℝ) • (1 : (Matrix (Fin d) (Fin d) ℂ))) :=
        smul_le_smul_of_nonneg_left hρbound hη.le
      _ = (η * ‖ρ‖) • (1 : (Matrix (Fin d) (Fin d) ℂ)) := smul_smul _ _ _
      _ ≤ r • (1 : (Matrix (Fin d) (Fin d) ℂ)) :=
        smul_le_smul_of_nonneg_right hηr Matrix.PosSemidef.one.nonneg
  refine ⟨η, hη, ?_⟩
  have hD' : r • (1 : (Matrix (Fin d) (Fin d) ℂ)) ≤ D := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hrD
  exact Matrix.le_iff.mp (hstep.trans hD')
private theorem strict_positive_feasible_faithful {d : ℕ} [NeZero d]
    (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (hStrict : ∀ X : (Matrix (Fin d) (Fin d) ℂ), X.PosSemidef → X ≠ 0 → (T X).PosDef)
    (C : ℝ) (x : (Matrix (Fin d) (Fin d) ℂ) × ℝ) (hx : x ∈ feasibleSet T C) :
    0 < x.2 ∧ x.1.PosDef := by
  obtain ⟨hρpos, hρtr⟩ := hx.1
  have hρne : x.1 ≠ 0 := by intro hz; simp [hz] at hρtr
  have hcρ : ((x.2 : ℂ) • x.1).PosDef := by
    convert (hStrict x.1 hρpos hρne).add_posSemidef hx.2.2 using 1
    abel
  have hcne : x.2 ≠ 0 := by
    intro hz
    have hdiag : (0 : ℂ) < ((x.2 : ℂ) • x.1) (0 : Fin d) 0 := hcρ.diag_pos
    simp [hz] at hdiag
  have hc : 0 < x.2 := lt_of_le_of_ne hx.2.1.1 (Ne.symm hcne)
  refine ⟨hc, ?_⟩
  have h := hcρ.smul (inv_pos.mpr hc)
  change ((x.2)⁻¹ • (x.2 • x.1)).PosDef at h
  simpa [smul_smul, inv_mul_cancel₀ hcne] using h
theorem strict_positive_perron_eigenmatrix {d : ℕ} [NeZero d]
    (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (hPos : ∀ X : (Matrix (Fin d) (Fin d) ℂ), X.PosSemidef → (T X).PosSemidef)
    (hStrict : ∀ X : (Matrix (Fin d) (Fin d) ℂ), X.PosSemidef → X ≠ 0 → (T X).PosDef) :
    ∃ (ρ : (Matrix (Fin d) (Fin d) ℂ)) (c : ℝ), ρ.PosDef ∧ Matrix.trace ρ = 1 ∧ 0 < c ∧
      T ρ = (c : ℂ) • ρ := by
  obtain ⟨C,hne⟩ := positive_has_feasible_constant T hPos
  obtain ⟨x,hx,hmin⟩ := collatz_minimum_exists T C hne
  obtain ⟨hc,hfaith⟩ := strict_positive_feasible_faithful T hStrict C x hx
  let ρ := x.1
  let c := x.2
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hc
  let D := (c : ℂ) • ρ - T ρ
  have hD : D.PosSemidef := hx.2.2
  have hDzero : D = 0 := by
    by_contra hneD
    let z := ρ + (c⁻¹ : ℝ) • T ρ
    have hz : z.PosSemidef :=
      hfaith.posSemidef.add ((hPos ρ hfaith.posSemidef).smul (inv_nonneg.mpr hc.le))
    have htr : 0 < (Matrix.trace z).re := by
      have hTtr := (hPos ρ hfaith.posSemidef).trace_nonneg.1
      have hρtr : Matrix.trace ρ = 1 := hx.1.2
      simp only [z, Matrix.trace_add, Matrix.trace_smul, hρtr, Complex.add_re,
        Complex.one_re, Complex.smul_re, smul_eq_mul]
      have hm : 0 ≤ c⁻¹ * (Matrix.trace (T ρ)).re :=
        mul_nonneg (inv_nonneg.mpr hc.le) hTtr
      linarith
    let D' := (c : ℂ) • z - T z
    have hD' : D'.PosDef := by
      have h := collatz_residual_strict T hStrict ρ c hc hD hneD
      have hi : ((c : ℂ)⁻¹) • T ρ = (c⁻¹ : ℝ) • T ρ := by
        ext i j
        simp [Matrix.smul_apply, Complex.real_smul]
      rw [hi] at h
      exact h
    obtain ⟨η0,hη0,hsmall⟩ := positive_definite_residual_lowering D' z hD' hz
    let η := min η0 (c/2)
    have hη : 0 < η := lt_min hη0 (by dsimp [c]; linarith)
    have hηc : η < c := (min_le_right η0 (c/2)).trans_lt (by linarith)
    have hηle : η ≤ η0 := min_le_left _ _
    have hηz : (η : ℝ) • z ≤ (η0 : ℝ) • z :=
      smul_le_smul_of_nonneg_right hηle hz.nonneg
    have hsmall' : (D' - (η : ℂ) • z).PosSemidef := by
      apply Matrix.le_iff.mp
      exact hηz.trans (Matrix.le_iff.mpr hsmall)
    have hnew : (((c - η : ℝ) : ℂ) • z - T z).PosSemidef := by
      convert hsmall' using 1
      simp only [D', Complex.ofReal_sub, sub_smul]
      abel
    let q := (Matrix.trace z).re
    let w := (q⁻¹ : ℝ) • z
    have hq : 0 < q := htr
    have hw : w.PosSemidef := hz.smul (inv_nonneg.mpr hq.le)
    have hqcast : (q : ℂ) = Matrix.trace z := by
      apply Complex.ext
      · rfl
      · simpa using hz.trace_nonneg.2
    have hwtr : Matrix.trace w = 1 := by
      simp only [w, Matrix.trace_smul]
      rw [← hqcast]
      rw [Complex.real_smul, ← Complex.ofReal_mul]
      simp [ne_of_gt hq]
    have hwnew : (((c - η : ℝ) : ℂ) • w - T w).PosSemidef := by
      have h := hnew.smul (inv_nonneg.mpr hq.le)
      have hid : ((c - η : ℝ) : ℂ) • w - T w =
          (q⁻¹ : ℝ) • (((c - η : ℝ) : ℂ) • z - T z) := by
        dsimp [w]
        rw [T.map_smul_of_tower, smul_sub]
        congr 1
        exact smul_comm _ _ _
      rw [hid]
      exact h
    have hwfeas : (w,c-η) ∈ feasibleSet T C := by
      refine ⟨⟨hw,hwtr⟩,⟨sub_nonneg.mpr hηc.le, ?_⟩,hwnew⟩
      exact (sub_le_self c hη.le).trans hx.2.1.2
    have hm := hmin (w,c-η) hwfeas
    dsimp [c] at hη hm
    linarith
  refine ⟨ρ,c,hfaith,hx.1.2,hc, ?_⟩
  exact (sub_eq_zero.mp hDzero).symm
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A] [Nontrivial A] [NormOneClass A]
private lemma faithful_perron_eigenvalue_bound (T : (A →ₗ[ℂ] A))
    (hPos : ∀ X, 0 ≤ X → 0 ≤ T X)
    (ρ : A) (hρ : IsStrictlyPositive ρ) (c : ℝ) (hc : 0 < c)
    (hEigen : T ρ = (c : ℂ) • ρ) (z : ℂ) (hz : Module.End.HasEigenvalue T z) : ‖z‖ ≤ c := by
  let U : (A →ₗ[ℂ] A) := ((c⁻¹ : ℝ) : ℂ) • T
  have hp : ∀ X, 0 ≤ X → 0 ≤ U X := by
    intro X hX
    change 0 ≤ (c⁻¹ : ℝ) • T X
    exact smul_nonneg (inv_nonneg.mpr hc.le) (hPos X hX)
  have hfix : U ρ = ρ := by
    change ((c⁻¹ : ℝ) : ℂ) • T ρ = ρ
    rw [hEigen, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hc),
      Complex.ofReal_one, one_smul]
  obtain ⟨v,hv⟩ := hz.exists_hasEigenvector
  have huv : Module.End.HasEigenvector U (((c⁻¹ : ℝ) : ℂ) * z) v := by
    refine ⟨?_,hv.2⟩
    rw [Module.End.mem_eigenspace_iff]
    change ((c⁻¹ : ℝ) : ℂ) • T v = _
    rw [hv.apply_eq_smul, smul_smul]
  have hb := faithful_fixed_eigenvalue_norm_le_one U hp ρ hρ hfix _ (Module.End.hasEigenvalue_of_hasEigenvector huv)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)] at hb
  simpa only [mul_one] using (inv_mul_le_iff₀ hc).mp hb
open scoped ComplexOrder MatrixOrder
private theorem matrix_faithful_perron_bound {d : ℕ} [NeZero d] (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (hPos : ∀ X, X.PosSemidef → (T X).PosSemidef)
    (ρ : (Matrix (Fin d) (Fin d) ℂ)) (hρ : ρ.PosDef) (c : ℝ) (hc : 0 < c)
    (hEigen : T ρ = (c : ℂ) • ρ) (z : ℂ)
    (hz : Module.End.HasEigenvalue T z) : ‖z‖ ≤ c := by
  letI : CStarAlgebra ((Matrix (Fin d) (Fin d) ℂ)) := {}
  apply faithful_perron_eigenvalue_bound T _ ρ hρ.isStrictlyPositive c hc hEigen z hz
  intro X hX
  change 0 ≤ T X
  exact (hPos X (Matrix.nonneg_iff_posSemidef.mp hX)).nonneg
private theorem faithful_perron_max_real {d : ℕ} [NeZero d] (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (hPos : ∀ X, X.PosSemidef → (T X).PosSemidef)
    (ρ : (Matrix (Fin d) (Fin d) ℂ)) (hρ : ρ.PosDef) (hρtr : Matrix.trace ρ = 1)
    (c : ℝ) (hc : 0 < c) (hEigen : T ρ = (c : ℂ) • ρ) :
    sSup (Complex.re '' {z : ℂ | z ∈ T.charpoly.roots}) = c := by
  have hρne : ρ ≠ 0 := by intro hz; simp [hz] at hρtr
  have hevc : Module.End.HasEigenvalue T (c : ℂ) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := ρ)
    exact ⟨Module.End.mem_eigenspace_iff.mpr hEigen,hρne⟩
  have hroot : (c : ℂ) ∈ T.charpoly.roots :=
    (Polynomial.mem_roots T.charpoly_monic.ne_zero).mpr
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly T (c : ℂ)).mp hevc)
  have hfinite : (Complex.re '' {z : ℂ | z ∈ T.charpoly.roots}).Finite :=
    by
      have hset : {z : ℂ | z ∈ T.charpoly.roots} = (T.charpoly.roots.toFinset : Set ℂ) := by
        ext z
        simp
      rw [hset]
      exact (T.charpoly.roots.toFinset.finite_toSet).image Complex.re
  have hmem : c ∈ Complex.re '' {z : ℂ | z ∈ T.charpoly.roots} := ⟨c,hroot,rfl⟩
  apply le_antisymm
  · apply csSup_le ⟨c,hmem⟩
    rintro _ ⟨z,hz,rfl⟩
    have hev := (Module.End.hasEigenvalue_iff_isRoot_charpoly T z).mpr
      ((Polynomial.mem_roots T.charpoly_monic.ne_zero).mp hz)
    exact (Complex.re_le_norm z).trans (matrix_faithful_perron_bound T hPos ρ hρ c hc hEigen z hev)
  · exact le_csSup hfinite.bddAbove hmem
private theorem regularized_perron_and_max_real {d : ℕ} [NeZero d]
    (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (hT : (KPositive 2 _ T)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (ρ : (Matrix (Fin d) (Fin d) ℂ)) (c : ℝ), ρ.PosDef ∧ Matrix.trace ρ = 1 ∧ 0 < c ∧
      ((T + (ε : ℂ) • ((Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight (1 : Matrix (Fin d) (Fin d) ℂ))) : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) ρ = (c : ℂ) • ρ ∧
      sSup (Complex.re '' {z : ℂ | z ∈ (T + (ε : ℂ) • ((Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight (1 : Matrix (Fin d) (Fin d) ℂ))).charpoly.roots}) = c := by
  let S := T + (ε : ℂ) • ((Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight (1 : Matrix (Fin d) (Fin d) ℂ))
  have h2S := regularization_twoPositive T hT ε hε.le
  have hPos : ∀ X, X.PosSemidef → (S X).PosSemidef := twoPositive_positive S h2S
  have hStrict : ∀ X, X.PosSemidef → X ≠ 0 → (S X).PosDef :=
    regularization_strictly_improving T hT ε hε
  obtain ⟨ρ,c,hρ,htr,hc,he⟩ := strict_positive_perron_eigenmatrix S hPos hStrict
  exact ⟨ρ,c,hρ,htr,hc,he,faithful_perron_max_real S hPos ρ hρ htr c hc he⟩
open scoped Matrix.Norms.L2Operator ENNReal NNReal
private lemma spectralRadius_eq_of_root_bounds {d : ℕ} [NeZero d] (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (c : ℝ) (hc : 0 ≤ c) (hroot : (c : ℂ) ∈ T.charpoly.roots)
    (hbound : ∀ z : ℂ, z ∈ T.charpoly.roots → ‖z‖ ≤ c) :
    spectralRadius ℂ T.toContinuousLinearMap = ENNReal.ofReal c := by
  have hspec (z : ℂ) : z ∈ spectrum ℂ T.toContinuousLinearMap ↔
      z ∈ T.charpoly.roots := by
    rw [ContinuousLinearMap.spectrum_eq]
    change z ∈ spectrum ℂ T ↔ _
    rw [← Module.End.hasEigenvalue_iff_mem_spectrum,
      Module.End.hasEigenvalue_iff_isRoot_charpoly,
      Polynomial.mem_roots T.charpoly_monic.ne_zero]
  rw [spectralRadius_eq_of_unital]
  apply le_antisymm
  · apply iSup₂_le
    intro z hz
    have hb := ENNReal.ofReal_le_ofReal (hbound z ((hspec z).mp hz))
    simpa only [← coe_nnnorm, ENNReal.ofReal_coe_nnreal] using hb
  · have h : (‖(c : ℂ)‖₊ : ℝ≥0∞) ≤
        ⨆ z ∈ spectrum ℂ T.toContinuousLinearMap, (‖z‖₊ : ℝ≥0∞) := by
      exact le_iSup₂_of_le (c : ℂ) ((hspec (c : ℂ)).mpr hroot) le_rfl
    simpa only [Complex.nnnorm_real, Real.nnnorm_of_nonneg hc,
      ← ENNReal.ofReal_eq_coe_nnreal hc] using h
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
theorem regularized_perron_certificate : RegularizedPerronGoal := by
  intro d hd T ε hε hT
  letI : NeZero d := ⟨ne_of_gt hd⟩
  have hTo : (KPositive 2 _ T) := hT
  obtain ⟨ρ,c,hρ,htr,hc,he,hmax⟩ := regularized_perron_and_max_real T hTo ε hε
  have h2S := regularization_twoPositive T hTo ε hε.le
  let S := T + (ε : ℂ) • ((Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight (1 : Matrix (Fin d) (Fin d) ℂ))
  have hPos : ∀ X, X.PosSemidef → (S X).PosSemidef := twoPositive_positive S h2S
  have hρne : ρ ≠ 0 := by intro hz; simp [hz] at htr
  have hevc : Module.End.HasEigenvalue S (c : ℂ) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := ρ)
    exact ⟨Module.End.mem_eigenspace_iff.mpr he,hρne⟩
  have hroot : (c : ℂ) ∈ S.charpoly.roots :=
    (Polynomial.mem_roots S.charpoly_monic.ne_zero).mpr
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly S (c : ℂ)).mp hevc)
  have hbound (z : ℂ) (hz : z ∈ S.charpoly.roots) : ‖z‖ ≤ c := by
    have hev := (Module.End.hasEigenvalue_iff_isRoot_charpoly S z).mpr
      ((Polynomial.mem_roots S.charpoly_monic.ne_zero).mp hz)
    exact matrix_faithful_perron_bound S hPos ρ hρ c hc he z hev
  have hradius := spectralRadius_eq_of_root_bounds S c hc.le hroot hbound
  refine ⟨{
    rho := ρ
    c := c
    rho_pos := hρ
    rho_trace := htr
    eigen := he
    c_pos := hc
    c_is_max := hmax.symm
    c_is_radius := hradius
  }⟩
end
end D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization

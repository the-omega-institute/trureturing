/- GID: D5/S3/Quantum/PredictionDepth/IncompleteObserverPhysicalCounterexample
   generality: G
   mirror-B: D5/B/S3/Quantum/PredictionDepth/IncompleteObserverPhysicalCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An incomplete finite observer has distinct symmetric states with equal readouts. -/

import D5.S3.Quantum.Tomography.InformationalCompletenessEquivalence

/- Library-search audit trail (2026-08-27):
   * Exact family hits `HermitianSpace`, `traceZeroHermitian`,
     `identityHermitian`, `scalarHermitian`, and `DensityState` provide the
     source's real Hermitian, traceless, identity, scalar, and physical-state
     carriers.
   * `informational_completeness_four_way` states the adjacent completeness
     equivalences, but its physical perturbation argument is private and its
     public statement does not expose the source's witnesses.
   * Repository searches for nonzero invisible directions together with
     symmetric density-state perturbations found no exact public D5 theorem.
   * Pinned Mathlib hits `Submodule.exists_mem_ne_zero_of_ne_bot`, the
     self-adjoint norm order bounds, and `Submodule.inner_left_of_mem_orthogonal`
     supply the construction below. No definition or abbreviation is added. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.PredictionDepth.IncompleteObserverPhysicalCounterexample

open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection

local instance matrixNormedAddCommGroup (d : Nat) :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixComplexInnerProductSpace (d : Nat) :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace (d : Nat) :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

/-- If the scalar-plus-centered visible operator system has a nontrivial
orthogonal residual, that residual contains a nonzero Hermitian direction.
Small symmetric perturbations of the maximally mixed state along this direction
are distinct density states with identical centered-effect signatures. -/
theorem incomplete_observer_physical_counterexample
    (d : Nat) [NeZero d] {Index : Type*}
    (centeredEffects : Index -> traceZeroHermitian d)
    (incomplete :
      (scalarHermitian d ⊔
        (Submodule.span ℝ (Set.range centeredEffects)).map
          (traceZeroHermitian d).subtype)ᗮ ≠ ⊥) :
    exists (D : HermitianSpace d) (eps : ℝ)
      (rhoPlus rhoMinus : DensityState (Fin d)),
      D ≠ 0 ∧
      D ∈ (scalarHermitian d ⊔
        (Submodule.span ℝ (Set.range centeredEffects)).map
          (traceZeroHermitian d).subtype)ᗮ ∧
      0 < eps ∧
      CStarMatrix.ofMatrix.symm rhoPlus.1 =
        (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) +
          (eps : ℂ) • D.1 ∧
      CStarMatrix.ofMatrix.symm rhoMinus.1 =
        (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) -
          (eps : ℂ) • D.1 ∧
      rhoPlus ≠ rhoMinus ∧
      (fun i =>
        (Matrix.trace
          (CStarMatrix.ofMatrix.symm rhoPlus.1 *
            (centeredEffects i).1.1)).re) =
        fun i =>
          (Matrix.trace
            (CStarMatrix.ofMatrix.symm rhoMinus.1 *
              (centeredEffects i).1.1)).re := by
  let centeredVisible := Submodule.span ℝ (Set.range centeredEffects)
  let visible := scalarHermitian d ⊔
    centeredVisible.map (traceZeroHermitian d).subtype
  let residual := visibleᗮ
  change residual ≠ ⊥ at incomplete
  obtain ⟨D, hDResidual, hDNonzero⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot incomplete
  have hIdentityVisible : identityHermitian d ∈ visible := by
    apply Submodule.mem_sup_left
    rw [scalarHermitian]
    exact Submodule.mem_span_singleton_self (identityHermitian d)
  have hDIdentity : inner ℝ D (identityHermitian d) = 0 :=
    Submodule.inner_left_of_mem_orthogonal hIdentityVisible hDResidual
  have hDTraceReal : Matrix.trace D.1 = ((Matrix.trace D.1).re : ℂ) := by
    have hDstar := D.2
    change star D.1 = D.1 at hDstar
    have hDHermitian : D.1ᴴ = D.1 := by
      simpa only [Matrix.star_eq_conjTranspose] using hDstar
    have hTraceStar : star (Matrix.trace D.1) = Matrix.trace D.1 := by
      calc
        star (Matrix.trace D.1) = Matrix.trace D.1ᴴ :=
          (Matrix.trace_conjTranspose D.1).symm
        _ = Matrix.trace D.1 := by rw [hDHermitian]
    exact (Complex.conj_eq_iff_re.mp hTraceStar).symm
  have hDInnerIdentity :
      inner ℝ D (identityHermitian d) = (Matrix.trace D.1).re := by
    have hDstar := D.2
    change star D.1 = D.1 at hDstar
    have hDHermitian : D.1ᴴ = D.1 := by
      simpa only [Matrix.star_eq_conjTranspose] using hDstar
    change (Matrix.trace
      ((1 : Matrix (Fin d) (Fin d) ℂ) * 1 * D.1ᴴ)).re = _
    rw [one_mul, one_mul, hDHermitian]
  have hDTrace : Matrix.trace D.1 = 0 := by
    rw [hDInnerIdentity] at hDIdentity
    rw [hDTraceReal, hDIdentity]
    rfl
  let D0 : traceZeroHermitian d := ⟨D, hDTrace⟩
  let A : CStarMatrix (Fin d) (Fin d) ℂ := CStarMatrix.ofMatrix D.1
  let c : ℝ := (d : ℝ)⁻¹
  let eps : ℝ := c / (2 * (‖A‖ + 1))
  have hc : 0 < c :=
    inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
  have hDenominator : 0 < 2 * (‖A‖ + 1) :=
    mul_pos (by norm_num) (by positivity)
  have hEps : 0 < eps := div_pos hc hDenominator
  have hProduct : eps * (‖A‖ + 1) = c / 2 := by
    dsimp only [eps]
    field_simp
  have hCoefficient : 0 ≤ c - eps * ‖A‖ := by
    have hStrict : eps * ‖A‖ < eps * (‖A‖ + 1) := by nlinarith
    rw [hProduct] at hStrict
    linarith
  have hASelf : IsSelfAdjoint A := by
    exact congrArg CStarMatrix.ofMatrix D.2
  have hLower :=
    IsSelfAdjoint.neg_algebraMap_norm_le_self (a := A) (ha := hASelf)
  have hLowerScaled := smul_le_smul_of_nonneg_left hLower hEps.le
  have hLowerShifted := add_le_add_left hLowerScaled
    ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c)
  have hPositiveLeft :
      0 ≤ eps •
            (-(algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) ‖A‖) +
          (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c := by
    have hEq :
        eps •
              (-(algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) ‖A‖) +
            (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c =
          (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ))
            (c - eps * ‖A‖) := by
      simp only [map_sub, map_mul, Algebra.smul_def]
      noncomm_ring
    rw [hEq]
    exact algebraMap_nonneg (β := CStarMatrix (Fin d) (Fin d) ℂ)
      hCoefficient
  have hPlus :
      0 ≤ (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c +
        (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A := by
    have hResult := hPositiveLeft.trans hLowerShifted
    rw [add_comm (eps • A)
      ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c)] at hResult
    simpa only [Algebra.smul_def] using hResult
  have hUpper :=
    IsSelfAdjoint.le_algebraMap_norm_self (a := A) (ha := hASelf)
  have hUpperScaled := smul_le_smul_of_nonneg_left hUpper hEps.le
  have hPositiveBase :
      0 ≤ (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
        eps • (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) ‖A‖ := by
    have hEq :
        (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
            eps • (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) ‖A‖ =
          (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ))
            (c - eps * ‖A‖) := by
      simp only [map_sub, map_mul, Algebra.smul_def]
    rw [hEq]
    exact algebraMap_nonneg (β := CStarMatrix (Fin d) (Fin d) ℂ)
      hCoefficient
  have hMinus :
      0 ≤ (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
        (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A := by
    have hBound := sub_le_sub_left hUpperScaled
      ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c)
    simp only [Algebra.smul_def] at hPositiveBase hBound ⊢
    exact hPositiveBase.trans hBound
  have hMatrixPlus :
      CStarMatrix.ofMatrix.symm
          ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c +
            (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A) =
        (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
          (eps : ℂ) • D.1 := by
    ext i j
    simp [A, Algebra.smul_def, CStarMatrix.algebraMap_apply,
      Matrix.algebraMap_matrix_apply, CStarMatrix.mul_apply, Matrix.mul_apply]
  have hMatrixMinus :
      CStarMatrix.ofMatrix.symm
          ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
            (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A) =
        (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) -
          (eps : ℂ) • D.1 := by
    ext i j
    simp [A, Algebra.smul_def, CStarMatrix.algebraMap_apply,
      Matrix.algebraMap_matrix_apply, CStarMatrix.mul_apply, Matrix.mul_apply]
  have hcComplex : (c : ℂ) = (d : ℂ)⁻¹ := by
    dsimp only [c]
    exact Complex.ofReal_inv (d : ℝ)
  have hTracePlus :
      Matrix.trace
          (CStarMatrix.ofMatrix.symm
            ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c +
              (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A)) = 1 := by
    rw [hMatrixPlus]
    simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
      hDTrace, Fintype.card_fin, smul_eq_mul]
    rw [hcComplex]
    simp [show (d : ℂ) ≠ 0 by exact_mod_cast NeZero.ne d]
  have hTraceMinus :
      Matrix.trace
          (CStarMatrix.ofMatrix.symm
            ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
              (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A)) = 1 := by
    rw [hMatrixMinus]
    simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
      hDTrace, Fintype.card_fin, smul_eq_mul]
    rw [hcComplex]
    simp [show (d : ℂ) ≠ 0 by exact_mod_cast NeZero.ne d]
  let rhoPlus : DensityState (Fin d) :=
    ⟨(algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c +
        (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A,
      hPlus, hTracePlus⟩
  let rhoMinus : DensityState (Fin d) :=
    ⟨(algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
        (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A,
      hMinus, hTraceMinus⟩
  have hStatesDistinct : rhoPlus ≠ rhoMinus := by
    intro hStates
    have hValues := congrArg (fun rho : DensityState (Fin d) => rho.1) hStates
    have hDifference : (2 * eps : ℝ) • A = 0 := by
      dsimp only [rhoPlus, rhoMinus] at hValues
      have hValues' :
          (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c + eps • A =
            (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c - eps • A := by
        simpa only [Algebra.smul_def] using hValues
      calc
        (2 * eps : ℝ) • A = 2 • (eps • A) :=
          (smul_smul (2 : ℝ) eps A).symm
        _ = eps • A + eps • A := two_smul ℝ (eps • A)
        _ = ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c + eps • A) -
            ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c - eps • A) := by
          abel
        _ = 0 := sub_eq_zero.mpr hValues'
    have hAZero : A = 0 :=
      (smul_eq_zero.mp hDifference).resolve_left (by positivity)
    apply hDNonzero
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.injective
    exact hAZero.trans
      (show (0 : CStarMatrix (Fin d) (Fin d) ℂ) =
        CStarMatrix.ofMatrix (0 : Matrix (Fin d) (Fin d) ℂ) from rfl)
  have hReadouts :
      (fun i =>
        (Matrix.trace
          (CStarMatrix.ofMatrix.symm rhoPlus.1 *
            (centeredEffects i).1.1)).re) =
        fun i =>
          (Matrix.trace
            (CStarMatrix.ofMatrix.symm rhoMinus.1 *
              (centeredEffects i).1.1)).re := by
    funext i
    have hCenteredVisible : centeredEffects i ∈ centeredVisible :=
      Submodule.subset_span (Set.mem_range_self i)
    have hVisible :
        (traceZeroHermitian d).subtype (centeredEffects i) ∈ visible :=
      Submodule.mem_sup_right
        ⟨centeredEffects i, hCenteredVisible, rfl⟩
    have hDInnerAmbient :
        inner ℝ D ((traceZeroHermitian d).subtype (centeredEffects i)) = 0 := by
      exact Submodule.inner_left_of_mem_orthogonal hVisible hDResidual
    have hDInner : inner ℝ D0 (centeredEffects i) = 0 := by
      simpa [D0] using hDInnerAmbient
    have hDstar := D.2
    change star D.1 = D.1 at hDstar
    have hDHermitian : D.1ᴴ = D.1 := by
      simpa only [Matrix.star_eq_conjTranspose] using hDstar
    have hDReadout :
        (Matrix.trace (D.1 * (centeredEffects i).1.1)).re = 0 := by
      have hInnerTrace :
          inner ℝ D0 (centeredEffects i) =
            (Matrix.trace (D.1 * (centeredEffects i).1.1)).re := by
        change (Matrix.trace
          ((centeredEffects i).1.1 * 1 * D.1ᴴ)).re = _
        rw [Matrix.mul_one, hDHermitian, Matrix.trace_mul_comm]
      rwa [hInnerTrace] at hDInner
    dsimp only [rhoPlus, rhoMinus]
    rw [hMatrixPlus, hMatrixMinus]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.trace_add, Matrix.trace_sub,
      Matrix.trace_smul, Complex.add_re, Complex.sub_re]
    have hScaledReadout :
        ((eps : ℂ) •
          Matrix.trace (D.1 * (centeredEffects i).1.1)).re = 0 := by
      rw [smul_eq_mul, Complex.mul_re]
      simp [hDReadout]
    rw [hScaledReadout]
    ring
  refine ⟨D, eps, rhoPlus, rhoMinus, hDNonzero, ?_, hEps, ?_, ?_,
    hStatesDistinct, hReadouts⟩
  · exact hDResidual
  · rw [hMatrixPlus, hcComplex]
  · rw [hMatrixMinus, hcComplex]

#print axioms incomplete_observer_physical_counterexample

end D5.S3.Quantum.PredictionDepth.IncompleteObserverPhysicalCounterexample

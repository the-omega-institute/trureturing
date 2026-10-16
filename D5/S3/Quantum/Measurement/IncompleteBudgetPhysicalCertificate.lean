/- GID: D5/S3/Quantum/Measurement/IncompleteBudgetPhysicalCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/IncompleteBudgetPhysicalCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonzero invisible direction yields explicit indistinguishable density states. -/

import D5.S3.Quantum.Tomography.InformationalCompletenessEquivalence

/- Library-search audit trail (2026-08-27):
   * Exact family hits `HermitianSpace`, `identityHermitian`, and the visible-span
     construction in `JointObserverVisibleResidual` supply the source carrier and
     residual semantics.
   * `InformationalCompletenessEquivalence` privately constructs maximally mixed
     perturbations inside one implication, but exposes no public certificate with
     the source's positivity, trace, distinction, and readout clauses.
   * Pinned Mathlib exact hits `IsSelfAdjoint.neg_algebraMap_norm_le_self` and
     `IsSelfAdjoint.le_algebraMap_norm_self` supply the order estimate. No
     end-to-end public theorem was found. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix MatrixOrder

namespace D5.S3.Quantum.Measurement.IncompleteBudgetPhysicalCertificate

open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false

local instance matrixNormedAddCommGroup (d : Nat) :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixComplexInnerProductSpace (d : Nat) :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace (d : Nat) :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

private theorem hermitian_trace_eq_re {d : Nat} (A : HermitianSpace d) :
    Matrix.trace A.1 = ((Matrix.trace A.1).re : ℂ) := by
  have hAstar := A.2
  change star A.1 = A.1 at hAstar
  have hA : A.1ᴴ = A.1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hAstar
  have hstar : star (Matrix.trace A.1) = Matrix.trace A.1 := by
    calc
      star (Matrix.trace A.1) = Matrix.trace A.1ᴴ :=
        (Matrix.trace_conjTranspose A.1).symm
      _ = Matrix.trace A.1 := by rw [hA]
  exact (Complex.conj_eq_iff_re.mp hstar).symm

private theorem hermitian_inner_eq_trace_mul {d : Nat}
    (A B : HermitianSpace d) :
    inner ℝ A B = (Matrix.trace (A.1 * B.1)).re := by
  have hAstar := A.2
  change star A.1 = A.1 at hAstar
  have hA : A.1ᴴ = A.1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hAstar
  change (Matrix.trace (B.1 * 1 * A.1ᴴ)).re = _
  rw [Matrix.mul_one, hA, Matrix.trace_mul_comm]

private theorem trace_mul_im_zero {d : Nat} (A B : HermitianSpace d) :
    (Matrix.trace (A.1 * B.1)).im = 0 := by
  have hAstar := A.2
  have hBstar := B.2
  change star A.1 = A.1 at hAstar
  change star B.1 = B.1 at hBstar
  have hA : A.1ᴴ = A.1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hAstar
  have hB : B.1ᴴ = B.1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hBstar
  have hstar : star (Matrix.trace (A.1 * B.1)) =
      Matrix.trace (A.1 * B.1) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      hA, hB, Matrix.trace_mul_comm]
  have him := congrArg Complex.im hstar
  change ((starRingEnd ℂ) (Matrix.trace (A.1 * B.1))).im = _ at him
  rw [Complex.conj_im] at him
  linarith

/-- A nonzero Hermitian direction in the orthogonal residual of a finite effect
budget produces explicit maximally mixed perturbations. Both perturbations are
positive trace-one matrices, they differ, and every declared Born readout agrees. -/
theorem incomplete_budget_physical_certificate
    (d : Nat) [NeZero d] {Index : Type*}
    (effects : Index -> {E : HermitianSpace d //
      E.1.PosSemidef ∧ (1 - E.1).PosSemidef})
    (D : HermitianSpace d) :
    let visible := Submodule.span ℝ
      (Set.insert (identityHermitian d) (Set.range fun i => (effects i).1))
    let residual := visibleᗮ
    D ∈ residual -> D ≠ 0 ->
      ∃ eps : ℝ, 0 < eps ∧
        let rhoPlus : Matrix (Fin d) (Fin d) ℂ :=
          ((d : ℂ)⁻¹) • 1 + (eps : ℂ) • D.1
        let rhoMinus : Matrix (Fin d) (Fin d) ℂ :=
          ((d : ℂ)⁻¹) • 1 - (eps : ℂ) • D.1
        0 ≤ CStarMatrix.ofMatrix rhoPlus ∧
          0 ≤ CStarMatrix.ofMatrix rhoMinus ∧
          Matrix.trace rhoPlus = 1 ∧
          Matrix.trace rhoMinus = 1 ∧
          rhoPlus ≠ rhoMinus ∧
          ∀ i, Matrix.trace (rhoPlus * (effects i).1.1) =
            Matrix.trace (rhoMinus * (effects i).1.1) := by
  classical
  dsimp only
  intro hResidual hDnonzero
  let visible := Submodule.span ℝ
    (Set.insert (identityHermitian d) (Set.range fun i => (effects i).1))
  have hIdentity : identityHermitian d ∈ visible :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hIdentityOrthogonal : inner ℝ D (identityHermitian d) = 0 :=
    (Submodule.mem_orthogonal' visible D).mp hResidual
      (identityHermitian d) hIdentity
  have hDtraceReal : (Matrix.trace D.1).re = 0 := by
    rw [hermitian_inner_eq_trace_mul] at hIdentityOrthogonal
    simpa only [identityHermitian, Matrix.mul_one] using hIdentityOrthogonal
  have hDtrace : Matrix.trace D.1 = 0 := by
    rw [hermitian_trace_eq_re D, hDtraceReal]
    rfl
  have hDreadout : ∀ i, Matrix.trace (D.1 * (effects i).1.1) = 0 := by
    intro i
    have hEffect : (effects i).1 ∈ visible :=
      Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self i))
    have hInner : inner ℝ D (effects i).1 = 0 :=
      (Submodule.mem_orthogonal' visible D).mp hResidual (effects i).1 hEffect
    apply Complex.ext
    · rw [hermitian_inner_eq_trace_mul] at hInner
      exact hInner
    · exact trace_mul_im_zero D (effects i).1
  let A : CStarMatrix (Fin d) (Fin d) ℂ := CStarMatrix.ofMatrix D.1
  let c : ℝ := (d : ℝ)⁻¹
  let eps : ℝ := c / (2 * (‖A‖ + 1))
  have hc : 0 < c :=
    inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
  have hdenominator : 0 < 2 * (‖A‖ + 1) :=
    mul_pos (by norm_num) (by positivity)
  have heps : 0 < eps := div_pos hc hdenominator
  have hproduct : eps * (‖A‖ + 1) = c / 2 := by
    dsimp only [eps]
    field_simp
  have hcoefficient : 0 ≤ c - eps * ‖A‖ := by
    have hstrict : eps * ‖A‖ < eps * (‖A‖ + 1) := by nlinarith
    rw [hproduct] at hstrict
    linarith
  have hAself : IsSelfAdjoint A := by
    exact congrArg CStarMatrix.ofMatrix D.2
  have hlower :=
    IsSelfAdjoint.neg_algebraMap_norm_le_self (a := A) (ha := hAself)
  have hlowerScaled := smul_le_smul_of_nonneg_left hlower heps.le
  have hlowerShifted := add_le_add_left hlowerScaled
    ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c)
  have hpositiveLeft :
      0 ≤ eps •
            (-(algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) ‖A‖) +
          (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c := by
    have heq :
        eps •
              (-(algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) ‖A‖) +
            (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c =
          (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ))
            (c - eps * ‖A‖) := by
      simp only [map_sub, map_mul, Algebra.smul_def]
      noncomm_ring
    rw [heq]
    exact algebraMap_nonneg (β := CStarMatrix (Fin d) (Fin d) ℂ)
      hcoefficient
  have hplus :
      0 ≤ (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c +
        (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A := by
    have hresult := hpositiveLeft.trans hlowerShifted
    rw [add_comm (eps • A)
      ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c)] at hresult
    simpa only [Algebra.smul_def] using hresult
  have hupper :=
    IsSelfAdjoint.le_algebraMap_norm_self (a := A) (ha := hAself)
  have hupperScaled := smul_le_smul_of_nonneg_left hupper heps.le
  have hpositiveBase :
      0 ≤ (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
        eps • (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) ‖A‖ := by
    have heq :
        (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
            eps • (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) ‖A‖ =
          (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ))
            (c - eps * ‖A‖) := by
      simp only [map_sub, map_mul, Algebra.smul_def]
    rw [heq]
    exact algebraMap_nonneg (β := CStarMatrix (Fin d) (Fin d) ℂ)
      hcoefficient
  have hminus :
      0 ≤ (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
        (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A := by
    have hbound := sub_le_sub_left hupperScaled
      ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c)
    simp only [Algebra.smul_def] at hpositiveBase hbound ⊢
    exact hpositiveBase.trans hbound
  have hmatrixPlus :
      CStarMatrix.ofMatrix.symm
          ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c +
            (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A) =
        (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
          (eps : ℂ) • D.1 := by
    ext i j
    simp [A, Algebra.smul_def, CStarMatrix.algebraMap_apply,
      Matrix.algebraMap_matrix_apply, CStarMatrix.mul_apply, Matrix.mul_apply]
  have hmatrixMinus :
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
  have hposPlus :
      0 ≤ CStarMatrix.ofMatrix
        ((d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) +
          (eps : ℂ) • D.1) := by
    rw [← hcComplex, ← hmatrixPlus]
    exact hplus
  have hposMinus :
      0 ≤ CStarMatrix.ofMatrix
        ((d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) -
          (eps : ℂ) • D.1) := by
    rw [← hcComplex, ← hmatrixMinus]
    exact hminus
  have htracePlus :
      Matrix.trace
          ((d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) +
            (eps : ℂ) • D.1) = 1 := by
    simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
      hDtrace, Fintype.card_fin, smul_eq_mul, mul_zero, add_zero]
    simp [show (d : ℂ) ≠ 0 by exact_mod_cast NeZero.ne d]
  have htraceMinus :
      Matrix.trace
          ((d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) -
            (eps : ℂ) • D.1) = 1 := by
    simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
      hDtrace, Fintype.card_fin, smul_eq_mul, mul_zero, sub_zero]
    simp [show (d : ℂ) ≠ 0 by exact_mod_cast NeZero.ne d]
  have hdistinct :
      (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) + (eps : ℂ) • D.1 ≠
        (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) - (eps : ℂ) • D.1 := by
    intro hequal
    have hscaled : (2 * (eps : ℂ)) • D.1 = 0 := by
      calc
        (2 * (eps : ℂ)) • D.1 =
            ((d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) +
              (eps : ℂ) • D.1) -
              ((d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) -
                (eps : ℂ) • D.1) := by module
        _ = 0 := sub_eq_zero.mpr hequal
    have hscalar : (2 * (eps : ℂ)) ≠ 0 := by
      exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr heps.ne')
    have hDzero : D.1 = 0 := (smul_eq_zero.mp hscaled).resolve_left hscalar
    exact hDnonzero (Subtype.ext hDzero)
  have hreadout : ∀ i,
      Matrix.trace
          (((d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) +
            (eps : ℂ) • D.1) * (effects i).1.1) =
        Matrix.trace
          (((d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) -
            (eps : ℂ) • D.1) * (effects i).1.1) := by
    intro i
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, hDreadout i,
      smul_zero, add_zero, sub_zero]
  exact ⟨eps, heps, hposPlus, hposMinus, htracePlus, htraceMinus,
    hdistinct, hreadout⟩

#print axioms incomplete_budget_physical_certificate

end D5.S3.Quantum.Measurement.IncompleteBudgetPhysicalCertificate

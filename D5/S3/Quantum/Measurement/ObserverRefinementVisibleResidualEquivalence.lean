/- GID: D5/S3/Quantum/Measurement/ObserverRefinementVisibleResidualEquivalence
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/ObserverRefinementVisibleResidualEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Quantum refinement is dual to visible and residual subspace inclusion. -/

import D5.S3.Quantum.Tomography.InformationalCompletenessEquivalence
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/- Library-search audit trail (2026-08-27):
   * Canonical `DensityState`, `HermitianSpace`, `identityHermitian`, and matrix
     inner-product instances are imported from the quantum tomography family.
   * Repository searches found global completeness, joint-observer, and abstract
     kernel-order results, but no physical-state refinement triple equivalence.
   * Pinned Mathlib's exact `Submodule.orthogonal_le_orthogonal_iff` proves the
     residual-visible order duality. The density-state bridge is proved below. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.ObserverRefinementVisibleResidualEquivalence

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection

attribute [local instance]
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixNormedAddCommGroup
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixComplexInnerProductSpace
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixRealInnerProductSpace

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

private theorem hermitian_inner_identity {d : Nat} (A : HermitianSpace d) :
    inner ℝ A (identityHermitian d) = (Matrix.trace A.1).re := by
  have hAstar := A.2
  change star A.1 = A.1 at hAstar
  have hA : A.1ᴴ = A.1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hAstar
  change (Matrix.trace ((1 : Matrix (Fin d) (Fin d) ℂ) * 1 * A.1ᴴ)).re = _
  rw [one_mul, one_mul, hA]

private theorem density_state_is_hermitian {d : Nat}
    (rho : DensityState (Fin d)) :
    (CStarMatrix.ofMatrix.symm rho.1).IsHermitian :=
  congrArg CStarMatrix.ofMatrix.symm rho.2.1.isSelfAdjoint.star_eq

/-- Refinement of density-state signatures, reverse inclusion of invisible
residuals, and inclusion of visible Hermitian spans are equivalent. -/
theorem observer_refinement_visible_residual_equivalence
    (d : Nat) [NeZero d] {IndexOne IndexTwo : Type*}
    (effectsOne : IndexOne -> HermitianSpace d)
    (effectsTwo : IndexTwo -> HermitianSpace d) :
    let stateOperator : DensityState (Fin d) -> HermitianSpace d :=
      fun rho =>
        ⟨CStarMatrix.ofMatrix.symm rho.1, density_state_is_hermitian rho⟩
    let signatureOne := fun rho : DensityState (Fin d) => fun i =>
      inner ℝ (stateOperator rho) (effectsOne i)
    let signatureTwo := fun rho : DensityState (Fin d) => fun i =>
      inner ℝ (stateOperator rho) (effectsTwo i)
    let visibleOne := Submodule.span ℝ
      (Set.insert (identityHermitian d) (Set.range effectsOne))
    let visibleTwo := Submodule.span ℝ
      (Set.insert (identityHermitian d) (Set.range effectsTwo))
    let residualOne := visibleOneᗮ
    let residualTwo := visibleTwoᗮ
    let refines := ∀ rho sigma,
      signatureTwo rho = signatureTwo sigma ->
        signatureOne rho = signatureOne sigma
    (refines ↔ residualTwo ≤ residualOne) ∧
      (residualTwo ≤ residualOne ↔ visibleOne ≤ visibleTwo) := by
  let stateOperator : DensityState (Fin d) -> HermitianSpace d :=
    fun rho =>
      ⟨CStarMatrix.ofMatrix.symm rho.1, density_state_is_hermitian rho⟩
  let signatureOne := fun rho : DensityState (Fin d) => fun i =>
    inner ℝ (stateOperator rho) (effectsOne i)
  let signatureTwo := fun rho : DensityState (Fin d) => fun i =>
    inner ℝ (stateOperator rho) (effectsTwo i)
  let visibleOne := Submodule.span ℝ
    (Set.insert (identityHermitian d) (Set.range effectsOne))
  let visibleTwo := Submodule.span ℝ
    (Set.insert (identityHermitian d) (Set.range effectsTwo))
  let residualOne := visibleOneᗮ
  let residualTwo := visibleTwoᗮ
  let refines := ∀ rho sigma,
    signatureTwo rho = signatureTwo sigma ->
      signatureOne rho = signatureOne sigma
  have state_difference_mem_residual_two
      {rho sigma : DensityState (Fin d)}
      (hSignature : signatureTwo rho = signatureTwo sigma) :
      stateOperator rho - stateOperator sigma ∈ residualTwo := by
    change stateOperator rho - stateOperator sigma ∈
      Submodule.orthogonal visibleTwo
    rw [Submodule.mem_orthogonal']
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hGenerator =>
        rcases hGenerator with (rfl | ⟨i, rfl⟩)
        · rw [inner_sub_left, hermitian_inner_identity,
            hermitian_inner_identity]
          have hRhoTrace : Matrix.trace (stateOperator rho).1 = 1 := by
            exact rho.2.2
          have hSigmaTrace : Matrix.trace (stateOperator sigma).1 = 1 := by
            exact sigma.2.2
          rw [hRhoTrace, hSigmaTrace]
          norm_num
        · have hi := congrFun hSignature i
          simpa only [signatureTwo, inner_sub_left, sub_eq_zero] using hi
    | zero => simp
    | add first second _ _ hFirst hSecond =>
        simp only [inner_add_right, hFirst, hSecond, add_zero]
    | smul scalar A _ hA =>
        simp only [real_inner_smul_right, hA, mul_zero]
  have hResidualVisible :
      residualTwo ≤ residualOne ↔ visibleOne ≤ visibleTwo := by
    exact Submodule.orthogonal_le_orthogonal_iff
  refine ⟨?_, hResidualVisible⟩
  constructor
  · intro hRefines D hDResidualTwo
    have hInnerIdentity : inner ℝ D (identityHermitian d) = 0 :=
      (Submodule.mem_orthogonal' visibleTwo D).mp hDResidualTwo
        (identityHermitian d)
        (Submodule.subset_span (Set.mem_insert _ _))
    have hTraceRe : (Matrix.trace D.1).re = 0 := by
      simpa only [hermitian_inner_identity] using hInnerIdentity
    have hTraceD : Matrix.trace D.1 = 0 := by
      rw [hermitian_trace_eq_re D, hTraceRe]
      rfl
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
    have hTracePlus :
        Matrix.trace
            (CStarMatrix.ofMatrix.symm
              ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c +
                (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A)) = 1 := by
      rw [hMatrixPlus]
      have hcComplex : (c : ℂ) = (d : ℂ)⁻¹ := by
        dsimp only [c]
        exact Complex.ofReal_inv (d : ℝ)
      simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
        hTraceD, Fintype.card_fin, smul_eq_mul]
      rw [hcComplex]
      simp [show (d : ℂ) ≠ 0 by exact_mod_cast NeZero.ne d]
    have hTraceMinus :
        Matrix.trace
            (CStarMatrix.ofMatrix.symm
              ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
                (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A)) = 1 := by
      rw [hMatrixMinus]
      have hcComplex : (c : ℂ) = (d : ℂ)⁻¹ := by
        dsimp only [c]
        exact Complex.ofReal_inv (d : ℝ)
      simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
        hTraceD, Fintype.card_fin, smul_eq_mul]
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
    have hMatrixDifference :
        CStarMatrix.ofMatrix.symm
              ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c +
                (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A) -
            CStarMatrix.ofMatrix.symm
              ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
                (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A) =
          ((2 * eps : ℝ) : ℂ) • D.1 := by
      rw [hMatrixPlus, hMatrixMinus]
      push_cast
      module
    have hStateDifference :
        stateOperator rhoPlus - stateOperator rhoMinus = (2 * eps) • D := by
      apply Subtype.ext
      change CStarMatrix.ofMatrix.symm rhoPlus.1 -
          CStarMatrix.ofMatrix.symm rhoMinus.1 =
            ((2 * eps : ℝ) : ℂ) • D.1
      dsimp only [rhoPlus, rhoMinus]
      exact hMatrixDifference
    have hSignatureTwo : signatureTwo rhoPlus = signatureTwo rhoMinus := by
      funext i
      have hInner : inner ℝ D (effectsTwo i) = 0 :=
        (Submodule.mem_orthogonal' visibleTwo D).mp hDResidualTwo
          (effectsTwo i)
          (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self i)))
      apply sub_eq_zero.mp
      change inner ℝ (stateOperator rhoPlus) (effectsTwo i) -
        inner ℝ (stateOperator rhoMinus) (effectsTwo i) = 0
      rw [← inner_sub_left, hStateDifference, real_inner_smul_left, hInner,
        mul_zero]
    have hSignatureOne : signatureOne rhoPlus = signatureOne rhoMinus :=
      hRefines rhoPlus rhoMinus hSignatureTwo
    change D ∈ Submodule.orthogonal visibleOne
    rw [Submodule.mem_orthogonal']
    intro E hE
    induction hE using Submodule.span_induction with
    | mem E hGenerator =>
        rcases hGenerator with (rfl | ⟨i, rfl⟩)
        · exact hInnerIdentity
        · have hi := congrFun hSignatureOne i
          have hScaled : (2 * eps) * inner ℝ D (effectsOne i) = 0 := by
            calc
              (2 * eps) * inner ℝ D (effectsOne i) =
                  inner ℝ ((2 * eps) • D) (effectsOne i) := by
                    rw [real_inner_smul_left]
              _ = inner ℝ (stateOperator rhoPlus - stateOperator rhoMinus)
                    (effectsOne i) := by rw [hStateDifference]
              _ = inner ℝ (stateOperator rhoPlus) (effectsOne i) -
                    inner ℝ (stateOperator rhoMinus) (effectsOne i) := by
                      rw [inner_sub_left]
              _ = 0 := sub_eq_zero.mpr hi
          exact (mul_eq_zero.mp hScaled).resolve_left (by positivity)
    | zero => simp
    | add first second _ _ hFirst hSecond =>
        simp only [inner_add_right, hFirst, hSecond, add_zero]
    | smul scalar E _ hE =>
        simp only [real_inner_smul_right, hE, mul_zero]
  · intro hResidualInclusion rho sigma hSignature
    have hDResidualTwo := state_difference_mem_residual_two hSignature
    have hDResidualOne := hResidualInclusion hDResidualTwo
    funext i
    have hInner :=
      (Submodule.mem_orthogonal' visibleOne
        (stateOperator rho - stateOperator sigma)).mp hDResidualOne
        (effectsOne i)
        (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self i)))
    simpa only [signatureOne, inner_sub_left, sub_eq_zero] using hInner

#print axioms observer_refinement_visible_residual_equivalence

end D5.S3.Quantum.Measurement.ObserverRefinementVisibleResidualEquivalence

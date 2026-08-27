/- GID: D5/S3/Quantum/PredictionDepth/TargetPredictionSufficiency
   generality: G
   mirror-B: D5/B/S3/Quantum/PredictionDepth/TargetPredictionSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Visible targets are signature-determined; invisible targets separate physical states. -/

import D5.S3.Quantum.Measurement.IncompleteBudgetPhysicalCertificate

/- Library-search audit trail (2026-08-27):
   * The canonical `HermitianSpace`, `identityHermitian`, `DensityState`, and
     identity-plus-effect visible span are imported rather than redeclared.
   * `IncompleteBudgetPhysicalCertificate` is a partial exact hit for turning a
     nonzero residual direction into positive trace-one perturbations with equal
     effect readouts; no target-relative public theorem was found.
   * Pinned Mathlib exact hits `Submodule.sub_starProjection_mem_orthogonal`,
     `Submodule.starProjection_eq_self_iff`, and `inner_self_ne_zero` construct
     a residual that pairs nontrivially with every target outside the span. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix MatrixOrder

namespace D5.S3.Quantum.PredictionDepth.TargetPredictionSufficiency

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Measurement.IncompleteBudgetPhysicalCertificate

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

/-- Every target observable in the identity-plus-effect visible span has an
expectation determined by the physical-state signature. Conversely, each
target outside that span supplies a trace-zero orthogonal residual direction
and two explicit physical states with equal signatures but unequal target
expectations. -/
theorem target_prediction_sufficiency
    (d : Nat) [NeZero d] {Index : Type*}
    (effects : Index -> {E : HermitianSpace d //
      E.1.PosSemidef ∧ (1 - E.1).PosSemidef})
    (targets : Submodule ℝ (HermitianSpace d)) :
    let visible := Submodule.span ℝ
      (Set.insert (identityHermitian d) (Set.range fun i => (effects i).1))
    ((targets ≤ visible) ->
      ∀ A : HermitianSpace d, A ∈ targets ->
        ∀ rho sigma : DensityState (Fin d),
          (∀ i, Matrix.trace
              (CStarMatrix.ofMatrix.symm rho.1 * (effects i).1.1) =
            Matrix.trace
              (CStarMatrix.ofMatrix.symm sigma.1 * (effects i).1.1)) ->
          Matrix.trace (CStarMatrix.ofMatrix.symm rho.1 * A.1) =
            Matrix.trace (CStarMatrix.ofMatrix.symm sigma.1 * A.1)) ∧
      (∀ A : HermitianSpace d, A ∉ visible ->
        ∃ (D : HermitianSpace d) (eps : ℝ)
            (rhoPlus rhoMinus : DensityState (Fin d)),
          Matrix.trace D.1 = 0 ∧
          D ∈ visibleᗮ ∧
          Matrix.trace (D.1 * A.1) ≠ 0 ∧
          0 < eps ∧
          CStarMatrix.ofMatrix.symm rhoPlus.1 =
            (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) +
              (eps : ℂ) • D.1 ∧
          CStarMatrix.ofMatrix.symm rhoMinus.1 =
            (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) -
              (eps : ℂ) • D.1 ∧
          (∀ i, Matrix.trace
              (CStarMatrix.ofMatrix.symm rhoPlus.1 * (effects i).1.1) =
            Matrix.trace
              (CStarMatrix.ofMatrix.symm rhoMinus.1 * (effects i).1.1)) ∧
          Matrix.trace (CStarMatrix.ofMatrix.symm rhoPlus.1 * A.1) ≠
            Matrix.trace (CStarMatrix.ofMatrix.symm rhoMinus.1 * A.1)) := by
  classical
  dsimp only
  let visible := Submodule.span ℝ
    (Set.insert (identityHermitian d) (Set.range fun i => (effects i).1))
  constructor
  · intro htargets A hA rho sigma hsignature
    have hVisible : A ∈ visible := htargets hA
    refine Submodule.span_induction (p := fun B : HermitianSpace d => fun _ =>
        Matrix.trace (CStarMatrix.ofMatrix.symm rho.1 * B.1) =
          Matrix.trace (CStarMatrix.ofMatrix.symm sigma.1 * B.1))
      ?_ ?_ ?_ ?_ hVisible
    · intro B hB
      rcases Set.mem_insert_iff.mp hB with hidentity | heffect
      · subst B
        have hRhoTrace :
            Matrix.trace (CStarMatrix.ofMatrix.symm rho.1) = 1 := rho.2.2
        have hSigmaTrace :
            Matrix.trace (CStarMatrix.ofMatrix.symm sigma.1) = 1 := sigma.2.2
        simpa only [identityHermitian, Matrix.mul_one] using
          hRhoTrace.trans hSigmaTrace.symm
      · obtain ⟨i, rfl⟩ := heffect
        exact hsignature i
    · simp
    · intro B C _ _ hB hC
      change Matrix.trace
          (CStarMatrix.ofMatrix.symm rho.1 * (B.1 + C.1)) =
        Matrix.trace (CStarMatrix.ofMatrix.symm sigma.1 * (B.1 + C.1))
      simp only [Matrix.mul_add, Matrix.trace_add, hB, hC]
    · intro r B _ hB
      change Matrix.trace
          (CStarMatrix.ofMatrix.symm rho.1 * ((r : ℂ) • B.1)) =
        Matrix.trace
          (CStarMatrix.ofMatrix.symm sigma.1 * ((r : ℂ) • B.1))
      simp only [Matrix.mul_smul, Matrix.trace_smul, hB]
  · intro A hAInvisible
    let D : HermitianSpace d := A - visible.starProjection A
    have hDResidual : D ∈ visibleᗮ :=
      visible.sub_starProjection_mem_orthogonal A
    have hDNonzero : D ≠ 0 := by
      intro hDZero
      apply hAInvisible
      apply visible.starProjection_eq_self_iff.mp
      symm
      apply sub_eq_zero.mp
      simpa only [D] using hDZero
    have hProjectionVisible : visible.starProjection A ∈ visible :=
      visible.starProjection_apply_mem A
    have hDProjection : inner ℝ D (visible.starProjection A) = 0 :=
      (Submodule.mem_orthogonal' visible D).mp hDResidual
        (visible.starProjection A) hProjectionVisible
    have hPairing : inner ℝ D A ≠ 0 := by
      have hDecomposition : A = D + visible.starProjection A := by
        dsimp only [D]
        abel
      rw [hDecomposition, inner_add_right, hDProjection, add_zero]
      exact inner_self_ne_zero.mpr hDNonzero
    have hTracePairing : Matrix.trace (D.1 * A.1) ≠ 0 := by
      intro hzero
      apply hPairing
      rw [hermitian_inner_eq_trace_mul, hzero]
      rfl
    have hIdentityVisible : identityHermitian d ∈ visible :=
      Submodule.subset_span (Set.mem_insert _ _)
    have hDIdentity : inner ℝ D (identityHermitian d) = 0 :=
      (Submodule.mem_orthogonal' visible D).mp hDResidual
        (identityHermitian d) hIdentityVisible
    have hDTraceReal : (Matrix.trace D.1).re = 0 := by
      rw [hermitian_inner_eq_trace_mul] at hDIdentity
      simpa only [identityHermitian, Matrix.mul_one] using hDIdentity
    have hDTrace : Matrix.trace D.1 = 0 := by
      rw [hermitian_trace_eq_re D, hDTraceReal]
      rfl
    obtain ⟨eps, hEps, hPosPlus, hPosMinus, hTracePlus, hTraceMinus,
        _hDistinct, hReadouts⟩ :=
      incomplete_budget_physical_certificate d effects D hDResidual hDNonzero
    let plusMatrix : Matrix (Fin d) (Fin d) ℂ :=
      (d : ℂ)⁻¹ • 1 + (eps : ℂ) • D.1
    let minusMatrix : Matrix (Fin d) (Fin d) ℂ :=
      (d : ℂ)⁻¹ • 1 - (eps : ℂ) • D.1
    let rhoPlus : DensityState (Fin d) :=
      ⟨CStarMatrix.ofMatrix plusMatrix, hPosPlus, hTracePlus⟩
    let rhoMinus : DensityState (Fin d) :=
      ⟨CStarMatrix.ofMatrix minusMatrix, hPosMinus, hTraceMinus⟩
    have hTargetDifferent :
        Matrix.trace (CStarMatrix.ofMatrix.symm rhoPlus.1 * A.1) ≠
          Matrix.trace (CStarMatrix.ofMatrix.symm rhoMinus.1 * A.1) := by
      intro hequal
      have hmatrixDifference :
          plusMatrix - minusMatrix = (2 * (eps : ℂ)) • D.1 := by
        dsimp only [plusMatrix, minusMatrix]
        module
      have htraceDifference :
          Matrix.trace (plusMatrix * A.1) -
              Matrix.trace (minusMatrix * A.1) =
            (2 * (eps : ℂ)) * Matrix.trace (D.1 * A.1) := by
        rw [← Matrix.trace_sub, ← Matrix.sub_mul, hmatrixDifference,
          Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      have hequalMatrices :
          Matrix.trace (plusMatrix * A.1) =
            Matrix.trace (minusMatrix * A.1) := by
        simpa only [rhoPlus, rhoMinus, Equiv.symm_apply_apply] using hequal
      have hscaled : (2 * (eps : ℂ)) * Matrix.trace (D.1 * A.1) = 0 := by
        rw [← htraceDifference]
        exact sub_eq_zero.mpr hequalMatrices
      exact (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr hEps.ne')) hTracePairing) hscaled
    refine ⟨D, eps, rhoPlus, rhoMinus, hDTrace, hDResidual,
      hTracePairing, hEps, ?_, ?_, ?_, hTargetDifferent⟩
    · rfl
    · rfl
    · exact hReadouts

#print axioms target_prediction_sufficiency

end D5.S3.Quantum.PredictionDepth.TargetPredictionSufficiency

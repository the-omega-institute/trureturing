/- GID: D5/S3/Quantum/Measurement/FirstReadOperatorNorm
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/FirstReadOperatorNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The trace-dual operator-norm form of the actual first-read error. -/

import D5.S3.Quantum.Measurement.MeasurementRelativeMenu
import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.LinearAlgebra.Complex.Module

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal ENNReal

namespace D5.S3.Quantum.Measurement.FirstReadOperatorNorm

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance (pureState)
open D5.S3.Quantum.Measurement.ActualModeProtocol
open D5.S3.Quantum.Measurement.MeasurementRelativeMenu

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def matrixMap (T : QuantumChannel ι ι) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
  CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
    (T.toCompletelyPositiveMap.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)

/-- The trace-pairing dual, defined on all matrices without selecting Kraus data. -/
def traceDual (T : QuantumChannel ι ι) (E : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => Matrix.trace (E * matrixMap T (Matrix.single j i 1))

private theorem traceDual_pairing (T : QuantumChannel ι ι) (E X : Matrix ι ι ℂ) :
    Matrix.trace (traceDual T E * X) = Matrix.trace (E * matrixMap T X) := by
  have hs (i j : ι) : Matrix.single i j (X i j) =
      X i j • Matrix.single i j (1 : ℂ) := by simp
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  simp_rw [hs, map_sum, Matrix.mul_sum, Matrix.trace_sum,
    map_smul, Matrix.mul_smul, Matrix.trace_smul]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, traceDual]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rfl

private theorem matrixMap_star (T : QuantumChannel ι ι) (X : Matrix ι ι ℂ) :
    matrixMap T Xᴴ = (matrixMap T X)ᴴ := by
  have hstar (A : CStarMatrix ι ι ℂ) :
      T.toCompletelyPositiveMap (star A) = star (T.toCompletelyPositiveMap A) := by
    let R := realPart A
    let I := imaginaryPart A
    have hr := R.property.map' T.toCompletelyPositiveMap
    have hi := I.property.map' T.toCompletelyPositiveMap
    have ha : A = (R : CStarMatrix ι ι ℂ) + Complex.I • (I : CStarMatrix ι ι ℂ) :=
      (realPart_add_I_smul_imaginaryPart A).symm
    rw [ha]
    simp only [star_add, star_smul, R.property.star_eq, I.property.star_eq,
      map_add, map_smul, hr.star_eq, hi.star_eq]
  exact hstar (CStarMatrix.ofMatrix X)

private theorem traceDual_hermitian (T : QuantumChannel ι ι)
    (E : Matrix ι ι ℂ) (hE : E.IsHermitian) : (traceDual T E).IsHermitian := by
  ext i j
  change star (Matrix.trace (E * matrixMap T (Matrix.single i j 1))) =
    Matrix.trace (E * matrixMap T (Matrix.single j i 1))
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hE.eq,
    ← matrixMap_star, Matrix.trace_mul_comm]
  simp

private theorem expectation_bound (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (ρ : DensityState ι) :
    |(Matrix.trace (A * CStarMatrix.ofMatrix.symm ρ.1)).re| ≤ ‖A‖ := by
  let X := CStarMatrix.ofMatrix.symm ρ.1
  have hX : X.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1)
  have htr : Matrix.trace X = 1 := ρ.2.2
  have upper := RHLinalg.trace_mul_nonneg_of_posSemidef
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hA.isSelfAdjoint.le_algebraMap_norm_self)) hX
  have lower := RHLinalg.trace_mul_nonneg_of_posSemidef
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hA.isSelfAdjoint.neg_algebraMap_norm_le_self)) hX
  simp only [Matrix.sub_mul, Matrix.neg_mul, Matrix.trace_sub, Matrix.trace_neg,
    Complex.sub_re, Complex.neg_re, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, htr] at upper lower
  simp only [Complex.real_smul, mul_one] at upper lower
  change 0 ≤ (((‖A‖ : ℂ) - (A * X).trace)).re at upper
  change 0 ≤ (((A * X).trace - -(‖A‖ : ℂ))).re at lower
  simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re] at upper lower
  change |(A * X).trace.re| ≤ ‖A‖
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem expectation_attains [Nonempty ι] (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ∃ ρ : DensityState ι,
      |(Matrix.trace (A * CStarMatrix.ofMatrix.symm ρ.1)).re| = ‖A‖ := by
  have hn : ‖A‖ = ‖fun i => (hA.eigenvalues i : ℂ)‖ := by
    conv_lhs => rw [hA.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal, Function.comp_def]
    rfl
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm (fun i => (hA.eigenvalues i : ℂ))).1
  let v : ι → ℂ := hA.eigenvectorBasis i
  have hv : star v ⬝ᵥ v = 1 := by
    change star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ ⇑(hA.eigenvectorBasis i) = 1
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hA.eigenvectorBasis.orthonormal.1 i]
    norm_num
  refine ⟨pureState v hv, ?_⟩
  change |(Matrix.trace (A * Matrix.vecMulVec v (star v))).re| = ‖A‖
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  change |(star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ A *ᵥ ⇑(hA.eigenvectorBasis i)).re| = ‖A‖
  have heig : (star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ A *ᵥ ⇑(hA.eigenvectorBasis i)).re =
      hA.eigenvalues i := (hA.eigenvalues_eq i).symm
  rw [heig]
  calc
    |hA.eigenvalues i| = ‖(hA.eigenvalues i : ℂ)‖ := by simp
    _ = ‖fun j => (hA.eigenvalues j : ℂ)‖ := hi
    _ = ‖A‖ := hn.symm

private theorem state_supremum [Nonempty ι] (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (⨆ ρ : DensityState ι, ENNReal.ofReal
      |(Matrix.trace (A * CStarMatrix.ofMatrix.symm ρ.1)).re|) = ENNReal.ofReal ‖A‖ := by
  apply le_antisymm
  · exact iSup_le fun ρ => ENNReal.ofReal_le_ofReal (expectation_bound A hA ρ)
  · obtain ⟨ρ, hρ⟩ := expectation_attains A hA
    exact le_iSup_of_le ρ (by rw [hρ])

private theorem event_hermitian (t : ℝ≥0) (J : Finset Mode) :
    (eventEffect t J).IsHermitian := by
  change (∑ s ∈ J, firstEffect t s).IsHermitian
  rw [Matrix.isHermitian_iff_isSelfAdjoint]
  apply isSelfAdjoint_sum
  intro s _
  exact (Matrix.isHermitian_conjTranspose_mul_mul _
    (show (projector s).IsHermitian by simp [projector, Matrix.IsHermitian])).isSelfAdjoint

/-- The second identity of the first-read theorem uses the Euclidean operator
norm and the trace dual of the same canonical channel used in actual histories. -/
theorem channel_error_eq_operator_norm (T : QuantumChannel Mode Mode) :
    channelError T = ⨆ t : ℝ≥0, ⨆ J : Finset Mode,
      ENNReal.ofReal ‖eventEffect t J - traceDual T (eventEffect t J)‖ := by
  rw [(channel_error_eq_event_expectation T).2]
  apply iSup_congr
  intro t
  apply iSup_congr
  intro J
  have he : (eventEffect t J - traceDual T (eventEffect t J)).IsHermitian :=
    (event_hermitian t J).sub (traceDual_hermitian T _ (event_hermitian t J))
  rw [← state_supremum _ he]
  apply iSup_congr
  intro ρ
  congr 2
  rw [Matrix.sub_mul, Matrix.trace_sub, traceDual_pairing, Matrix.mul_sub,
    Matrix.trace_sub]
  rfl

#print axioms channel_error_eq_operator_norm

end D5.S3.Quantum.Measurement.FirstReadOperatorNorm

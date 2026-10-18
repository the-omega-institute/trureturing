/- GID: D5/S3/Quantum/Matrix/CfmMonotonicityCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CfmMonotonicityCertificate
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: none
   digest: Rational witnesses exclude both matrix monotonicity directions. -/

/-
admission_basis: escape-witness
proof_shape: finite_certificate: content; escape_witness: finite_certificate
proof_shape: cfc_rationalFunction: content; escape_witness: finite_certificate
proof_shape: not_matrix_monotone: content; escape_witness: finite_certificate
-/

import D5.S3.Quantum.Matrix.RadialConvexity
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
The rational functional-calculus expression is checked directly on positive definite complex
matrices. All matrix inverses below are certified by exact multiplication, without numerical
spectral approximation.
-/

set_option autoImplicit false

noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder

namespace D5.S3.Quantum.Matrix.CfmMonotonicityCertificate

/-- The real scalar function in the counterexample. -/
def scalarFunction (t : ℝ) : ℝ :=
  (t + 1) / (t + 3) + (t + 1) / (2 * t + 4) -
    (1 / 20000 : ℝ) * ((t + 1) / (3 * t + 5))

/-- The rational matrix expression for the proposed scalar counterexample. -/
def rationalFunction {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (A + 1) * (A + 3)⁻¹ + (A + 1) * ((2 : ℝ) • A + 4)⁻¹ -
    (1 / 20000 : ℝ) • ((A + 1) * ((3 : ℝ) • A + 5)⁻¹)

/-- The smaller positive definite matrix in the finite counterexample. -/
def lowerMatrix : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![1 / 3, 1, 3]

/-- The larger positive definite matrix in the finite counterexample. -/
def upperMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 25 : ℝ) • !![11, 4, 8; 4, 31, 12; 8, 12, 99]

/-- A vector detecting the failure of Loewner positivity. -/
def testVector : Fin 3 → ℂ := ![-35, 48, -15]

/-- The real Hermitian quadratic form at the separating vector. -/
def quadraticReadout (X : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  (star testVector ⬝ᵥ (X *ᵥ testVector)).re

private def rankVector : Fin 3 → ℂ := ![2, 3, 6]

private theorem rank_increment :
    upperMatrix - lowerMatrix = (2 / 75 : ℝ) • vecMulVec rankVector (star rankVector) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerMatrix, upperMatrix, rankVector, diagonal, vecMulVec, map_ofNat]

private theorem increment_psd : (upperMatrix - lowerMatrix).PosSemidef := by
  rw [rank_increment]
  exact (posSemidef_vecMulVec_self_star rankVector).smul (by norm_num)

private theorem lower_pos : lowerMatrix.PosDef := by
  apply PosDef.diagonal
  intro i
  fin_cases i <;> norm_num

private theorem upper_pos : upperMatrix.PosDef := by
  have h := lower_pos.add_posSemidef increment_psd
  simpa only [add_sub_cancel] using h

private theorem inv_lower_1 : (lowerMatrix + 3)⁻¹ =
    (!![3 / 10, 0, 0; 0, 1 / 4, 0; 0, 0, 1 / 6] : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerMatrix, Matrix.mul_apply, Fin.sum_univ_succ, diagonal, Matrix.ofNat_apply, Matrix.one_apply]

private theorem inv_lower_2 : ((2 : ℝ) • lowerMatrix + 4)⁻¹ =
    (!![3 / 14, 0, 0; 0, 1 / 6, 0; 0, 0, 1 / 10] : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerMatrix, Matrix.mul_apply, Fin.sum_univ_succ, diagonal, Matrix.ofNat_apply, Matrix.one_apply]

private theorem inv_lower_3 : ((3 : ℝ) • lowerMatrix + 5)⁻¹ =
    (!![1 / 6, 0, 0; 0, 1 / 8, 0; 0, 0, 1 / 14] : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerMatrix, Matrix.mul_apply, Fin.sum_univ_succ, diagonal, Matrix.ofNat_apply, Matrix.one_apply]

private theorem inv_upper_1 : (upperMatrix + 3)⁻¹ =
    (!![183 / 626, -3 / 313, -4 / 313; -3 / 313, 149 / 626, -5 / 313;
      -4 / 313, -5 / 313, 91 / 626] : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.ofNat_apply, Matrix.one_apply]

private theorem inv_upper_2 : ((2 : ℝ) • upperMatrix + 4)⁻¹ =
    (!![477 / 2306, -10 / 1153, -12 / 1153; -10 / 1153, 361 / 2306, -14 / 1153;
      -12 / 1153, -14 / 1153, 197 / 2306] : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.ofNat_apply, Matrix.one_apply]

private theorem inv_upper_3 : ((3 : ℝ) • upperMatrix + 5)⁻¹ =
    (!![907 / 5666, -21 / 2833, -24 / 2833; -21 / 2833, 661 / 5666, -27 / 2833;
      -24 / 2833, -27 / 2833, 343 / 5666] : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.ofNat_apply, Matrix.one_apply]

private theorem quadratic_certificate :
    quadraticReadout (rationalFunction upperMatrix - rationalFunction lowerMatrix) =
      -(2 / 111549375 : ℝ) := by
  unfold quadraticReadout rationalFunction
  rw [inv_lower_1, inv_lower_2, inv_lower_3, inv_upper_1, inv_upper_2, inv_upper_3]
  norm_num [testVector, lowerMatrix, upperMatrix, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, diagonal, Matrix.ofNat_apply, Matrix.one_apply]

private theorem positive_diagonal_certificate :
    0 < ((rationalFunction upperMatrix - rationalFunction lowerMatrix) 0 0).re := by
  unfold rationalFunction
  rw [inv_lower_1, inv_lower_2, inv_lower_3, inv_upper_1, inv_upper_2, inv_upper_3]
  norm_num [testVector, lowerMatrix, upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ, diagonal, Matrix.ofNat_apply, Matrix.one_apply]

/-- Ordered positive definite matrices give both a negative quadratic form and a positive
entry in their rational-function increment, excluding either monotonicity direction. -/
theorem finite_certificate :
    lowerMatrix.PosDef ∧ upperMatrix.PosDef ∧ lowerMatrix ≤ upperMatrix ∧
    quadraticReadout (rationalFunction upperMatrix - rationalFunction lowerMatrix) =
      -(2 / 111549375 : ℝ) ∧
    0 < ((rationalFunction upperMatrix - rationalFunction lowerMatrix) 0 0).re := by
  exact ⟨lower_pos, upper_pos, increment_psd, quadratic_certificate,
    positive_diagonal_certificate⟩

private theorem cfc_rational_term {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    cfc (fun t : ℝ => (t + 1) / (a * t + b)) A =
      (A + 1) * (a • A + b • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ := by
  have hs : (spectrum ℝ A).Finite := by
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ A) := hs.continuousOn _
  have hn : ∀ x ∈ spectrum ℝ A, a * x + b ≠ 0 := by
    intro x hx
    exact ne_of_gt (add_pos_of_nonneg_of_pos
      (mul_nonneg ha (spectrum_nonneg_of_nonneg hA.posSemidef.nonneg hx)) hb)
  rw [cfc_map_div (p := IsSelfAdjoint) (fun t : ℝ => t + 1)
      (fun t : ℝ => a * t + b) A hn (hc _) (hc _) hA.isHermitian.isSelfAdjoint,
    cfc_add_const (p := IsSelfAdjoint) 1 (fun t : ℝ => t) A (hc _) hA.isHermitian.isSelfAdjoint,
    cfc_id' (p := IsSelfAdjoint) ℝ A hA.isHermitian.isSelfAdjoint,
    cfc_add_const (p := IsSelfAdjoint) b (fun t : ℝ => a * t) A (hc _) hA.isHermitian.isSelfAdjoint,
    cfc_const_mul_id (p := IsSelfAdjoint) a A hA.isHermitian.isSelfAdjoint,
    ← Matrix.nonsing_inv_eq_ringInverse]
  simp only [map_one, Algebra.algebraMap_eq_smul_one]

/-- Positive definite spectral functional calculus equals the rational matrix expression. -/
theorem cfc_rationalFunction {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) : cfc scalarFunction A = rationalFunction A := by
  have hs : (spectrum ℝ A).Finite := by
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ A) := hs.continuousOn _
  unfold scalarFunction
  rw [cfc_sub _ _ A (hc _) (hc _), cfc_add A _ _ (hc _) (hc _),
    cfc_const_mul _ _ A (hc _)]
  rw [show (fun t : ℝ => (t + 1) / (t + 3)) =
      (fun t : ℝ => (t + 1) / (1 * t + 3)) by ext; simp]
  rw [cfc_rational_term hA 1 3 (by norm_num) (by norm_num),
    cfc_rational_term hA 2 4 (by norm_num) (by norm_num),
    cfc_rational_term hA 3 5 (by norm_num) (by norm_num)]
  simp only [rationalFunction, one_smul, ← Algebra.algebraMap_eq_smul_one, map_ofNat]

/-- The real rational function has neither Loewner monotonicity direction in dimension three. -/
theorem not_matrix_monotone : ¬ RadialConvexity.MatrixMonotoneDegree 3 scalarFunction := by
  rintro (hinc | hdec)
  · rcases finite_certificate with ⟨hA, hB, hle, hq, _⟩
    have hp := Matrix.le_iff.mp (hinc lowerMatrix upperMatrix hA hB hle)
    change (cfc scalarFunction upperMatrix - cfc scalarFunction lowerMatrix).PosSemidef at hp
    rw [cfc_rationalFunction hA, cfc_rationalFunction hB] at hp
    have hn := hp.re_dotProduct_nonneg testVector
    change 0 ≤ quadraticReadout (rationalFunction upperMatrix - rationalFunction lowerMatrix) at hn
    rw [hq] at hn
    norm_num at hn
  · rcases finite_certificate with ⟨hA, hB, hle, _, hd⟩
    have hp := Matrix.le_iff.mp (hdec lowerMatrix upperMatrix hA hB hle)
    change (cfc scalarFunction lowerMatrix - cfc scalarFunction upperMatrix).PosSemidef at hp
    rw [cfc_rationalFunction hA, cfc_rationalFunction hB] at hp
    have hn := (Complex.nonneg_iff.mp (hp.diag_nonneg (i := 0))).1
    simp only [Matrix.sub_apply, Complex.sub_re] at hn hd
    linarith

end D5.S3.Quantum.Matrix.CfmMonotonicityCertificate

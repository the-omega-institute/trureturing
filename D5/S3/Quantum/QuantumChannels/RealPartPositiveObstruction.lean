/- GID: D5/S3/Quantum/QuantumChannels/RealPartPositiveObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/RealPartPositiveObstruction
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Transpose symmetrization preserves real readouts but has a negative Choi direction. -/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Quantum.QuantumChannels.RealPartPositiveObstruction

open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complex-linear symmetrization; on Hermitian inputs this is entrywise real part. -/
def symmetrize : MatrixMap n n ℂ where
  toFun X := (2 : ℂ)⁻¹ • (X + X.transpose)
  map_add' X Y := by simp [Matrix.transpose_add, smul_add]; abel
  map_smul' c X := by simp [Matrix.transpose_smul, smul_smul, mul_comm]

private theorem symmetrize_positive {X : Matrix n n ℂ} (h : X.PosSemidef) :
    (symmetrize X).PosSemidef := by
  exact (h.add h.transpose).smul (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩ : (0 : ℂ) ≤ (2 : ℂ)⁻¹)

private theorem symmetrize_trace (X : Matrix n n ℂ) :
    Matrix.trace (symmetrize X) = Matrix.trace X := by
  simp [symmetrize, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_transpose]
  ring

private theorem hermitian_real_part (X : Matrix n n ℂ) (h : X.IsHermitian) (i j : n) :
    symmetrize X i j = (X i j).re := by
  have he : star (X j i) = X i j := congrFun (congrFun h i) j
  apply Complex.ext <;> simp [symmetrize, Matrix.transpose_apply, Complex.mul_re,
    Complex.mul_im, Complex.inv_re, Complex.inv_im] <;>
      have hr := congrArg Complex.re he <;>
      have hi := congrArg Complex.im he <;> simp at hr hi <;> linarith

/-- The antisymmetric tensor supported on two distinct coordinates. -/
def antisymmetric (a b : n) : n × n → ℂ :=
  Pi.single (a, b) 1 - Pi.single (b, a) 1

private theorem choi_entry (i j k l : n) :
    MatrixMap.choi_matrix (symmetrize (n := n)) (i,j) (k,l) =
      (2 : ℂ)⁻¹ * ((if j = i ∧ l = k then 1 else 0) +
        (if j = k ∧ l = i then 1 else 0)) := by
  simp only [MatrixMap.choi_matrix, symmetrize, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul,
    Matrix.single_apply]

private theorem choi_negative_eigenvector (a b : n) (hab : a ≠ b) :
    (MatrixMap.choi_matrix (symmetrize (n := n))).mulVec (antisymmetric a b) =
      (- (2 : ℂ)⁻¹) • antisymmetric a b := by
  classical
  ext p
  rcases p with ⟨i,j⟩
  simp only [antisymmetric, Matrix.mulVec_sub, Matrix.mulVec_single_one,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply, choi_entry]
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    by_cases hja : j = a <;> by_cases hjb : j = b <;>
    simp [Pi.single_apply, Prod.mk.injEq, hia, hib, hja, hjb, hab, Ne.symm hab] <;>
    simp_all <;> aesop

/-- A positive trace-preserving map retaining every symmetric trace readout need not be CP.
The exhibited eigenvalue is for the unnormalized Choi matrix. -/
theorem real_part_readout_obstruction (a b : n) (hab : a ≠ b) :
    (∀ X : Matrix n n ℂ, X.PosSemidef → (symmetrize X).PosSemidef) ∧
    (∀ X : Matrix n n ℂ, Matrix.trace (symmetrize X) = Matrix.trace X) ∧
    (∀ X : Matrix n n ℂ, X.IsHermitian →
      ∀ i j, symmetrize X i j = (X i j).re) ∧
    (∀ E X : Matrix n n ℂ, E.transpose = E →
      Matrix.trace (E * symmetrize X) = Matrix.trace (E * X)) ∧
    (MatrixMap.choi_matrix (symmetrize (n := n))).mulVec (antisymmetric a b) =
      (- (2 : ℂ)⁻¹) • antisymmetric a b ∧
    (((Fintype.card n : ℂ)⁻¹) • MatrixMap.choi_matrix (symmetrize (n := n))).mulVec
        (antisymmetric a b) =
      (-1 / (2 * (Fintype.card n : ℂ))) • antisymmetric a b ∧
    ¬ MatrixMap.IsCompletelyPositive (symmetrize (n := n)) := by
  refine ⟨fun _ h => symmetrize_positive h, symmetrize_trace,
    hermitian_real_part, ?_, choi_negative_eigenvector a b hab, ?_, ?_⟩
  · intro E X hE
    have ht : Matrix.trace (E * X.transpose) = Matrix.trace (E * X) := by
      rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose,
        hE, Matrix.trace_mul_comm]
    simp [symmetrize, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul,
      Matrix.trace_add, ht]
    ring
  · rw [Matrix.smul_mulVec, choi_negative_eigenvector a b hab, smul_smul]
    congr 1
    simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm]
  · intro hcp
    have hp := (MatrixMap.choi_PSD_iff_CP_map _).mp hcp
    have hnonneg := hp.dotProduct_mulVec_nonneg (antisymmetric a b)
    rw [choi_negative_eigenvector a b hab] at hnonneg
    have hvalue : star (antisymmetric a b) ⬝ᵥ
        ((- (2 : ℂ)⁻¹) • antisymmetric a b) = -1 := by
      simp [antisymmetric, dotProduct_sub, sub_dotProduct, dotProduct_smul,
        star_sub, Pi.star_single, hab, Ne.symm hab]
      norm_num
    rw [hvalue] at hnonneg
    norm_num at hnonneg

end D5.S3.Quantum.QuantumChannels.RealPartPositiveObstruction

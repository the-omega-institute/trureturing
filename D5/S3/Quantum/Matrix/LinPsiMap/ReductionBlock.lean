/- GID: D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/LinPsiMap/ReductionBlock
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Positivity of the conjugate reduction block via skew matrix units. -/

import D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound

/-! The reduction block is a positive sum of congruences. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Matrix.LinPsiMap
open D5.S3.Quantum.Matrix.LinGProperty
open D5.S3.Quantum.Schatten
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The trace reflection map in Lin's Example 3.6. -/
def psi {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (2 * T.trace) • 1 - T

def skew {n : ℕ} (k l : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single k l 1 - Matrix.single l k 1

private theorem skew_sandwich {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (k l : Fin n) :
    skew k l * T * (skew k l)ᴴ =
      Matrix.single k k (T l l) - Matrix.single k l (T l k) -
      Matrix.single l k (T k l) + Matrix.single l l (T k k) := by
  classical
  simp only [skew, conjTranspose_sub, conjTranspose_single, star_one,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.single_mul_mul_single, one_mul, mul_one]
  abel

theorem skew_sum {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    ((1 / 2 : ℝ) : ℂ) • (∑ k, ∑ l, skew k l * T * (skew k l)ᴴ) =
      T.trace • 1 - Tᵀ := by
  classical
  simp_rw [skew_sandwich]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.add_apply, Matrix.sub_apply,
    smul_eq_mul, Matrix.transpose_apply]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  by_cases hij : i = j
  · subst j
    simp [Matrix.single, ite_and, Matrix.trace, Matrix.diag_apply]
    ring
  · simp [Matrix.single, ite_and, hij, Ne.symm hij]
    ring

/-- Applying the reduction map after conjugation preserves positivity of the whole block. -/
theorem reduction_block_posSemidef {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ}
    (hW : (fromBlocks A X Xᴴ B).PosSemidef) :
    (fromBlocks (A.trace • 1 - A) (Xᴴ.trace • 1 - Xᴴ)
      (X.trace • 1 - X) (B.trace • 1 - B)).PosSemidef := by
  classical
  let W := fromBlocks A X Xᴴ B
  let C := Wᵀ
  have hC : C.PosSemidef := hW.transpose
  let D (k l : Fin n) := fromBlocks (skew k l) 0 0 (skew k l)
  have hp : (((1 / 2 : ℝ) : ℂ) • (∑ k, ∑ l, D k l * C * (D k l)ᴴ)).PosSemidef :=
    (Matrix.posSemidef_sum _ fun k _ => Matrix.posSemidef_sum _ fun l _ =>
      hC.mul_mul_conjTranspose_same (D k l)).smul (Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1/2))
  have he : ((1 / 2 : ℝ) : ℂ) • (∑ k, ∑ l, D k l * C * (D k l)ᴴ) =
      fromBlocks (A.trace • 1 - A) (Xᴴ.trace • 1 - Xᴴ)
        (X.trace • 1 - X) (B.trace • 1 - B) := by
    have hs (T : Matrix (Fin n) (Fin n) ℂ) := skew_sum Tᵀ
    simp only [trace_transpose, transpose_transpose] at hs
    dsimp [D, C, W]
    simp only [fromBlocks_transpose, fromBlocks_conjTranspose, conjTranspose_zero,
      fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
    ext (i | i) (j | j)
    · simpa only [Matrix.smul_apply, Matrix.sum_apply, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, smul_eq_mul,
        Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
        congrArg (fun M => M i j) (hs A)
    · simpa only [Matrix.smul_apply, Matrix.sum_apply, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, smul_eq_mul,
        Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
        congrArg (fun M => M i j) (hs Xᴴ)
    · simpa only [Matrix.smul_apply, Matrix.sum_apply, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, smul_eq_mul,
        Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
        congrArg (fun M => M i j) (hs X)
    · simpa only [Matrix.smul_apply, Matrix.sum_apply, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, smul_eq_mul,
        Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
        congrArg (fun M => M i j) (hs B)

  exact he ▸ hp

end D5.S3.Quantum.Matrix.LinPsiMap

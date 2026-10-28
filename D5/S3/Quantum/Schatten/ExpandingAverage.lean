/- GID: D5/S3/Quantum/Schatten/ExpandingAverage
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/ExpandingAverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The balanced average of an invertible matrix and its inverse adjoint is expanding. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

noncomputable section
open Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Schatten

/-- The positive real scaling of the balanced inverse-adjoint average. -/
def inverseAdjointAverage {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℝ) • (t • W + t⁻¹ • (W⁻¹)ᴴ)

private theorem inverseAdjointAverage_gram_identity {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : IsUnit W.det) (t : ℝ) (ht : t ≠ 0) :
    (inverseAdjointAverage W t)ᴴ * inverseAdjointAverage W t - 1 =
      (1 / 4 : ℝ) • ((t • W - t⁻¹ • (W⁻¹)ᴴ)ᴴ *
        (t • W - t⁻¹ • (W⁻¹)ᴴ)) := by
  let X := t • W
  let Y := t⁻¹ • (W⁻¹)ᴴ
  have hcross₁ : Xᴴ * Y = 1 := by
    change (t • W)ᴴ * (t⁻¹ • (W⁻¹)ᴴ) = 1
    rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
      smul_smul, mul_inv_cancel₀ ht, one_smul,
      ← conjTranspose_mul, Matrix.nonsing_inv_mul W hW, conjTranspose_one]
  have hcross₂ : Yᴴ * X = 1 := by
    change (t⁻¹ • (W⁻¹)ᴴ)ᴴ * (t • W) = 1
    rw [conjTranspose_smul, star_trivial, conjTranspose_conjTranspose,
      smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ ht,
      one_smul, Matrix.nonsing_inv_mul W hW]
  change ((1 / 2 : ℝ) • (X + Y))ᴴ * ((1 / 2 : ℝ) • (X + Y)) - 1 =
    (1 / 4 : ℝ) • ((X - Y)ᴴ * (X - Y))
  simp only [conjTranspose_smul, star_trivial,
    conjTranspose_add, conjTranspose_sub, smul_mul_assoc, mul_smul_comm,
    smul_smul, add_mul, mul_add, sub_mul, mul_sub, hcross₁, hcross₂]
  module

/-- Every balanced inverse-adjoint average has all singular values at least one. -/
theorem inverseAdjointAverage_expanding {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : IsUnit W.det) (t : ℝ) (ht : 0 < t) :
    ((inverseAdjointAverage W t)ᴴ * inverseAdjointAverage W t - 1).PosSemidef := by
  rw [inverseAdjointAverage_gram_identity W hW t ht.ne']
  exact (Matrix.posSemidef_conjTranspose_mul_self _).smul (by norm_num : (0 : ℝ) ≤ 1 / 4)

end D5.S3.Quantum.Schatten

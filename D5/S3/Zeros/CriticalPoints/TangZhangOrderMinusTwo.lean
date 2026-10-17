/- GID: D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Charpoly.Basic]
   utility: none
   digest: The inverse-square critical-point inequality and its collinearity equality case. -/

import D5.S3.Zeros.CriticalPoints.SchurFrobeniusInequality
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! Polynomial, matrix and collinearity identities for the inverse-square conjecture. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo

open Polynomial Matrix Complex
open scoped ComplexConjugate

noncomputable def P {n : ℕ} (z : Fin n → ℂ) : Polynomial ℂ :=
  Polynomial.X * ∏ j, (Polynomial.X - Polynomial.C (z j))

def claim : Prop := ∀ (n : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ), (∀ j, z j ≠ 0) →
    (((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖⁻¹ ^ 2)).sum ≤
      3 * ∑ j, ‖z j‖⁻¹ ^ 2 + ‖∑ j, (z j)⁻¹‖ ^ 2) ∧
    ((((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖⁻¹ ^ 2)).sum =
      3 * ∑ j, ‖z j‖⁻¹ ^ 2 + ‖∑ j, (z j)⁻¹‖ ^ 2) ↔
        ∀ j, ∃ r : ℝ, z j = (r : ℂ) * z ⟨0, hn⟩)

private def J (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun _ _ => 1

private theorem J_sq (n : ℕ) : J n * J n = (n : ℂ) • J n := by
  ext i j
  simp [J, Matrix.mul_apply]

private theorem J_conjTranspose (n : ℕ) : (J n)ᴴ = J n := by
  ext i j
  simp [J, Matrix.conjTranspose_apply]

private theorem square_root_matrix (n : ℕ) (c : ℂ) (hc : 2 * c + (n : ℂ) * c ^ 2 = 1) :
    (1 + c • J n) * (1 + c • J n) = 1 + J n := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul,
    Matrix.smul_mul, Matrix.mul_smul, J_sq, smul_smul, smul_smul]
  have he : c • J n + (c • J n + (c * (c * n)) • J n) = J n := by
    rw [← add_smul, ← add_smul]
    convert one_smul ℂ (J n) using 1
    congr 1
    linear_combination hc
  calc
    1 + c • J n + (c • J n + (c * (c * n)) • J n) =
        1 + (c • J n + (c • J n + (c * (c * n)) • J n)) := by abel
    _ = 1 + J n := by rw [he]

private theorem inverse_matrix (n : ℕ) (c d : ℂ) (hcd : c + d + (n : ℂ) * c * d = 0) :
    (1 + c • J n) * (1 + d • J n) = 1 := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul,
    Matrix.smul_mul, Matrix.mul_smul, J_sq, smul_smul, smul_smul]
  have he : d • J n + (c • J n + (c * (d * n)) • J n) = 0 := by
    rw [← add_smul, ← add_smul]
    convert zero_smul ℂ (J n) using 1
    congr 1
    linear_combination hcd
  calc
    1 + d • J n + (c • J n + (c * (d * n)) • J n) =
        1 + (d • J n + (c • J n + (c * (d * n)) • J n)) := by abel
    _ = 1 := by rw [he, add_zero]

end D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo

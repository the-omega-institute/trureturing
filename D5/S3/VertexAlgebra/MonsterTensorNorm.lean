/- GID: D5/S3/VertexAlgebra/MonsterTensorNorm
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/MonsterTensorNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric trace Gram data determines the cubic tensor Frobenius square sum. -/

import Mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.MonsterTensorNorm

open Matrix

/-- The coordinate square sum of a finite family of square matrices. -/
def matrixFamilySquareSum {n : ℕ} (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ a, ∑ b, (T i a b) ^ 2

/-- For symmetric matrices, a constant diagonal trace Gram identity fixes the full
coordinate Frobenius square sum. -/
theorem symmetric_trace_gram_square_sum {n : ℕ}
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hSymm : ∀ i, (T i).IsSymm)
    (hTrace : ∀ i, Matrix.trace (T i * T i) = c) :
    matrixFamilySquareSum T = n * c := by
  unfold matrixFamilySquareSum
  calc
    ∑ i, ∑ a, ∑ b, (T i a b) ^ 2 = ∑ i, Matrix.trace (T i * T i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have hs := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M a b) (hSymm i).eq
      simp only [Matrix.transpose_apply] at hs
      rw [hs]
      ring
    _ = ∑ _i : Fin n, c := by simp_rw [hTrace]
    _ = n * c := by simp

/-- The numerical Monster dimension and Norton trace coefficient yield the
Frobenius square claimed for the normalized cubic tensor. -/
theorem moonshine_tensor_square_sum
    (T : Fin (196883 : ℕ) → Matrix (Fin (196883 : ℕ)) (Fin (196883 : ℕ)) ℝ)
    (hSymm : ∀ i, (T i).IsSymm)
    (hTrace : ∀ i, Matrix.trace (T i * T i) = (4620 : ℝ) - 2 / 3) :
    matrixFamilySquareSum T = (2728404614 : ℝ) / 3 := by
  rw [symmetric_trace_gram_square_sum T ((4620 : ℝ) - 2 / 3) hSymm hTrace]
  norm_num

end D5.S3.VertexAlgebra.MonsterTensorNorm

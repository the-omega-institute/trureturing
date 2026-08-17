/- GID: D5/S3/PrimeForms/Obstructions/NegativeDeterminantSquareObstruction
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Obstructions/NegativeDeterminantSquareObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Determinant minus one obstructs an integer matrix square. -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum

namespace D5.S3.PrimeForms.Obstructions.NegativeDeterminantSquareObstruction

/-- An integer matrix with determinant `-1` cannot be the square of another integer matrix. -/
theorem det_neg_one_not_matrix_square
    {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℤ}
    (hdet : M.det = -1) :
    ¬ ∃ A : Matrix n n ℤ, A * A = M := by
  rintro ⟨A, rfl⟩
  have hnonneg : 0 ≤ Matrix.det (A * A) := by
    rw [Matrix.det_mul]
    exact mul_self_nonneg A.det
  rw [hdet] at hnonneg
  norm_num at hnonneg

end D5.S3.PrimeForms.Obstructions.NegativeDeterminantSquareObstruction

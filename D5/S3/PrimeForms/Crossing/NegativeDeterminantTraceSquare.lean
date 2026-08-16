/- GID: D5/S3/PrimeForms/Crossing/NegativeDeterminantTraceSquare
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Crossing/NegativeDeterminantTraceSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A determinant-minus-one matrix has trace(A^2) = trace(A)^2 + 2. -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring

namespace D5.S3.PrimeForms.Crossing.NegativeDeterminantTraceSquare

/-- A two-by-two integer matrix of determinant `-1` has
`trace (A^2) = trace(A)^2 + 2`. -/
theorem trace_square_of_det_neg_one (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : Matrix.det A = -1) :
    Matrix.trace (A ^ 2) = Matrix.trace A ^ 2 + 2 := by
  calc
    Matrix.trace (A ^ 2) = Matrix.trace A ^ 2 - 2 * Matrix.det A := by
      simp only [pow_two, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply,
        Fin.sum_univ_two]
      ring
    _ = Matrix.trace A ^ 2 + 2 := by rw [hdet]; ring

end D5.S3.PrimeForms.Crossing.NegativeDeterminantTraceSquare

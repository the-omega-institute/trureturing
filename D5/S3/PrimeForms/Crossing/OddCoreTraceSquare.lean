/- GID: D5/S3/PrimeForms/Crossing/OddCoreTraceSquare
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Crossing/OddCoreTraceSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Determinant negative one forces the two-dimensional trace-square identity. -/

import Mathlib

namespace D5.S3.PrimeForms.Crossing.OddCoreTraceSquare

/-- For a two-dimensional integer matrix of determinant `-1`, the trace of its square is the
square of its trace plus two. This is the trace-square clause of the odd-core theorem in E.38. -/
theorem trace_square_eq_of_det_neg_one (delta : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : delta.det = -1) :
    Matrix.trace (delta * delta) = Matrix.trace delta ^ 2 + 2 := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  nlinarith

end D5.S3.PrimeForms.Crossing.OddCoreTraceSquare

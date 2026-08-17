/- GID: D5/S1/Eigenstructure/FibonacciMatrixDiscriminant
   generality: I
   mirror-B: D5/B/S1/Eigenstructure/FibonacciMatrixDiscriminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Fibonacci matrix has trace one, determinant minus one, and discriminant five. -/

import D5.S1.Scale.FibonacciEigen
import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc

namespace D5.S1.Eigenstructure.FibonacciMatrixDiscriminant

open D5.S1.Scale

/-- The Fibonacci substitution matrix has trace `1`, determinant `-1`, and discriminant `5`. -/
theorem fibonacci_substitution_trace_det_discriminant :
    Matrix.trace fibonacciSubstitution = 1 ∧
      Matrix.det fibonacciSubstitution = -1 ∧
        Matrix.discr fibonacciSubstitution = 5 := by
  norm_num [fibonacciSubstitution, Matrix.trace_fin_two, Matrix.det_fin_two,
    Matrix.discr_fin_two]

#print axioms fibonacci_substitution_trace_det_discriminant

end D5.S1.Eigenstructure.FibonacciMatrixDiscriminant

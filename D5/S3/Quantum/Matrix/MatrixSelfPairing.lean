/- GID: D5/S3/Quantum/Matrix/MatrixSelfPairing
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/MatrixSelfPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pair positive trace-one matrix weights with norm squares and their nonnegativity. -/

import D5.S3.Quantum.GNSMatrix

/- Library-search audit trail (2026-08-17):
   * The exact repository hit `D5.S3.Quantum.GNSMatrix.gns_matrix_identity`
     supplies the equality and is applied below.
   * Pinned Mathlib grep and a corrected Loogle statement query found no full
     trace/square-root identity; LeanSearch's live endpoint returned HTTP 404.
   * The explicit nonnegativity clause is discharged by the standard order
     facts for a real norm square.
-/

namespace D5.S3.Quantum.Matrix.MatrixSelfPairing

open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open Matrix

/-- A positive trace-one matrix pairs every operation with itself as a nonnegative norm square. -/
theorem matrix_self_pairing_and_nonnegative {d : Type*} [Fintype d] [DecidableEq d]
    (rho x : Matrix d d ℂ) (hRho : rho.PosSemidef)
    (hTrace : Matrix.trace rho = 1) :
    Matrix.trace (rho * Matrix.conjTranspose x * x) = (‖x * CFC.sqrt rho‖ : ℂ) ^ 2 ∧
      0 ≤ ‖x * CFC.sqrt rho‖ ^ 2 := by
  constructor
  · exact D5.S3.Quantum.GNSMatrix.gns_matrix_identity rho x hRho hTrace
  · positivity

example :
    (1 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef ∧
      Matrix.trace (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
  constructor
  · exact Matrix.PosSemidef.one
  · simp [Matrix.trace]

example :
    Matrix.trace
        ((1 : Matrix (Fin 1) (Fin 1) ℂ) *
          Matrix.conjTranspose (0 : Matrix (Fin 1) (Fin 1) ℂ) * 0) =
        (‖(0 : Matrix (Fin 1) (Fin 1) ℂ) *
          CFC.sqrt (1 : Matrix (Fin 1) (Fin 1) ℂ)‖ : ℂ) ^ 2 ∧
      0 ≤ ‖(0 : Matrix (Fin 1) (Fin 1) ℂ) *
        CFC.sqrt (1 : Matrix (Fin 1) (Fin 1) ℂ)‖ ^ 2 := by
  apply matrix_self_pairing_and_nonnegative
  · exact Matrix.PosSemidef.one
  · simp [Matrix.trace]

#print axioms matrix_self_pairing_and_nonnegative

end D5.S3.Quantum.Matrix.MatrixSelfPairing

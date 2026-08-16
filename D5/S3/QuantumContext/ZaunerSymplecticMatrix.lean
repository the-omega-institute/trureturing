/- GID: D5/S3/QuantumContext/ZaunerSymplecticMatrix
   generality: I
   mirror-B: D5/B/S3/QuantumContext/ZaunerSymplecticMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certify the explicit modular Zauner matrix and its fixed vector. -/

/- Library-search audit trail (2026-08-16):
   * Searches of D5 and the pinned mathlib tree found no theorem for the explicit matrix
     `!![6, 23; 19, 17]` over `ZMod 24`, its order, or its fixed vector.
   * Loogle's determinant-pattern query found `Matrix.det_fin_two_of`; the equivalent
     `Matrix.det_fin_two` and `Matrix.trace_fin_two` are imported and applied below.
   * Loogle's `mulVec` notation query failed to elaborate, and the LeanSearch API endpoint
     returned HTTP 404. The remaining finite equalities are checked by kernel reduction.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

namespace D5.S3.QuantumContext.ZaunerSymplecticMatrix

/-- Two-dimensional matrices over the residue ring modulo twenty-four. -/
abbrev ModularPhaseMatrix := Matrix (Fin 2) (Fin 2) (ZMod 24)

/-- The explicit Zauner matrix from the instance-level source clause. -/
def zaunerMatrix : ModularPhaseMatrix := !![6, 23; 19, 17]

/-- The residue vector singled out as a fixed point by the source clause. -/
def zaunerFixedVector : Fin 2 -> ZMod 24 := ![8, 16]

/-- Exact instance certificate for the displayed modular matrix. It has determinant one,
trace minus one, satisfies its cyclotomic quadratic relation, has exact order three, and fixes
the displayed vector. This does not classify the full value-preserving group from the source. -/
theorem zauner_symplectic_matrix_certificate :
    Matrix.det zaunerMatrix = 1 ∧
      Matrix.trace zaunerMatrix = -1 ∧
      zaunerMatrix ^ 2 + zaunerMatrix + 1 = 0 ∧
      zaunerMatrix ^ 3 = 1 ∧
      zaunerMatrix ≠ 1 ∧
      Matrix.mulVec zaunerMatrix zaunerFixedVector = zaunerFixedVector := by
  constructor
  · rw [Matrix.det_fin_two]
    decide
  constructor
  · rw [Matrix.trace_fin_two]
    decide
  decide

end D5.S3.QuantumContext.ZaunerSymplecticMatrix

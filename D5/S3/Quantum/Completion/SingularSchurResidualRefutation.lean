/- GID: D5/S3/Quantum/Completion/SingularSchurResidualRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Completion/SingularSchurResidualRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=atom:13dea0618bd938376949228d1a89d8b44fdec522579df36cba81c7ae9381fd96; result=D5/S3/Quantum/Completion/SingularSchurResidualRefutation.result; claim=D5/S3/Quantum/Completion/SingularSchurResidualRefutation.claim
   digest: A nonnegative singular Schur residual does not certify positive semidefiniteness without the range condition. -/

import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Matrix.Positivity

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Completion.SingularSchurResidualRefutation

/-- The singular two-by-two block from the C129 boundary counterexample. -/
def bad : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 1]

/-- The naive residual test accepts the lower-right entry of this block. -/
def claim : Prop := bad.PosSemidef

private def witness : Fin 2 → ℂ := ![1, -1]

private theorem quadratic : star witness ⬝ᵥ (bad *ᵥ witness) = (-1 : ℂ) := by
  norm_num [bad, witness, dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Pi.star_apply]

/-- The displayed singular block is not positive semidefinite. -/
theorem result : ¬ claim := by
  intro h
  have hq := h.dotProduct_mulVec_nonneg witness
  rw [quadratic] at hq
  norm_num [Complex.le_def] at hq

end D5.S3.Quantum.Completion.SingularSchurResidualRefutation

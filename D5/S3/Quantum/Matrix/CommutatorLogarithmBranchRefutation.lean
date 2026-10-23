/- GID: D5/S3/Quantum/Matrix/CommutatorLogarithmBranchRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/CommutatorLogarithmBranchRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/CommutatorLogarithmBranchRefutation.claim; result=D5/S3/Quantum/Matrix/CommutatorLogarithmBranchRefutation.result; claim=D5/S3/Quantum/Matrix/CommutatorLogarithmBranchRefutation.claim
   digest: No exponential-dependent logarithm maps recover every complex halved commutator. -/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section

namespace D5.S3.Quantum.Matrix.CommutatorLogarithmBranchRefutation

/-- The commutator identity with both generalized logarithms determined by the exponential. -/
def claim : Prop :=
  ∃ ΛL ΛR : Matrix (Fin 2) (Fin 2) ℂ →
      (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ),
    ∀ G : Matrix (Fin 2) (Fin 2) ℂ,
      (1 / 2 : ℂ) • (LinearMap.mulLeft ℂ G - LinearMap.mulRight ℂ G) =
        (1 / 2 : ℂ) • (ΛL (NormedSpace.exp G) - ΛR (NormedSpace.exp G))

/-- The complex commutator cannot be recovered uniformly from the matrix exponential. -/
theorem result : ¬ claim := by
  rintro ⟨ΛL, ΛR, h⟩
  have hexp : NormedSpace.exp
      (Matrix.diagonal ![0, 2 * Real.pi * Complex.I] : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [Matrix.exp_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  have hzero := h 0
  have hone := h (Matrix.diagonal ![0, 2 * Real.pi * Complex.I])
  rw [NormedSpace.exp_zero] at hzero
  rw [hexp] at hone
  have heq := hzero.trans hone.symm
  have hentry := congrArg
    (fun f : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ =>
      f (Matrix.single 0 1 1) 0 1) heq
  simp [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.mul_diagonal] at hentry

end D5.S3.Quantum.Matrix.CommutatorLogarithmBranchRefutation

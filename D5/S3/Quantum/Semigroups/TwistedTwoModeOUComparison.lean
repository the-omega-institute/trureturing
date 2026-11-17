/- GID: D5/S3/Quantum/Semigroups/TwistedTwoModeOUComparison
   generality: G
   mirror-B: D5/B/S3/Quantum/Semigroups/TwistedTwoModeOUComparison
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Complex two-mode fermionic pure-state attenuation for unital Kraus maps. -/

import D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation

/-! Quantitative pure-state loss for the two literal Jordan-Wigner modes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix Kronecker
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation

namespace D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison

private def localJump : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;0,0]
private def signZ : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![-1,1]

/-- The modes on the ordered basis 00,01,10,11. -/
def modeJump (i : Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ![localJump ⊗ₖ 1, signZ ⊗ₖ localJump] i

/-- The quartic directional budget, including both complex determinant terms. -/
def directionalBudget (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) : ℝ :=
  (Complex.normSq (ψ (0,0)) + Complex.normSq (ψ (0,1)))^2 +
  (Complex.normSq (ψ (0,0)) + Complex.normSq (ψ (1,0)))^2 +
  2 * Complex.normSq (ψ (0,0) * ψ (1,1)) +
  2 * Complex.normSq (ψ (0,1) * ψ (1,0))

private theorem mode_car (i : Fin 2) :
    modeJump i * modeJump i = 0 ∧
    modeJump i * (modeJump i).conjTranspose +
      (modeJump i).conjTranspose * modeJump i = 1 := by
  fin_cases i <;> constructor <;> ext ⟨a,b⟩ ⟨c,d⟩ <;>
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [modeJump, localJump, signZ, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply]

private theorem mode_maps_commute (q : ℝ) (hq : 0 ≤ q)
    (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    jumpMap (modeJump 0) q (jumpMap (modeJump 1) q X) =
      jumpMap (modeJump 1) q (jumpMap (modeJump 0) q X) := by
  simp only [jumpMap_apply _ _ hq]
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [jumpFilter, modeJump, localJump, signZ, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply] <;> ring

end D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison

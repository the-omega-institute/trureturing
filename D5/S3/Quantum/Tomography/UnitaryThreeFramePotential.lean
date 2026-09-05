/- GID: D5/S3/Quantum/Tomography/UnitaryThreeFramePotential
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/UnitaryThreeFramePotential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every three-by-three unitary has entrywise fourth frame potential at least one, with a rational sum-of-squares proof. -/

import D5.S3.Quantum.Tomography.ZaunerCompletionFibre
import Mathlib.Tactic.FinCases

/- Library-search audit trail (2026-09-03):
   * Reuses Matrix row Gram and `Complex.normSq`.
   * Repository and pinned Mathlib searches found no project theorem exposing
     the required `3 x 3` fourth-potential lower bound in this normalization.
   * The proof uses the exact three-variable variance identity instead of
     introducing a parallel collision definition.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.UnitaryThreeFramePotential

open Matrix

private theorem row_normSq_sum_one
    (B : Matrix (Fin 3) (Fin 3) ℂ)
    (hB : B * Bᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ))
    (i : Fin 3) :
    ∑ j, Complex.normSq (B i j) = 1 := by
  have hEntry := congrFun (congrFun hB i) i
  have hReal := congrArg Complex.re hEntry
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.normSq_eq_conj_mul_self, mul_comm] using hReal

/-- Rowwise fourth-potential lower bound for a three-by-three unitary. -/
theorem unitaryThree_row_fourthPotential_ge_one_third
    (B : Matrix (Fin 3) (Fin 3) ℂ)
    (hB : B * Bᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ))
    (i : Fin 3) :
    (3 : ℝ)⁻¹ ≤ ∑ j, (Complex.normSq (B i j)) ^ 2 := by
  have hSum := row_normSq_sum_one B hB i
  rw [Fin.sum_univ_three] at hSum ⊢
  have h01 := sq_nonneg
    (Complex.normSq (B i 0) - Complex.normSq (B i 1))
  have h02 := sq_nonneg
    (Complex.normSq (B i 0) - Complex.normSq (B i 2))
  have h12 := sq_nonneg
    (Complex.normSq (B i 1) - Complex.normSq (B i 2))
  norm_num at hSum ⊢
  nlinarith

/-- Every `3 x 3` unitary has fourth frame potential at least one. This is the
exact scalar estimate used by the Zauner block-diagonal collision separator. -/
theorem unitaryThree_fourthPotential_ge_one
    (B : Matrix (Fin 3) (Fin 3) ℂ)
    (hB : B * Bᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ)) :
    1 ≤ ∑ i, ∑ j, (Complex.normSq (B i j)) ^ 2 := by
  have h0 := unitaryThree_row_fourthPotential_ge_one_third B hB 0
  have h1 := unitaryThree_row_fourthPotential_ge_one_third B hB 1
  have h2 := unitaryThree_row_fourthPotential_ge_one_third B hB 2
  rw [Fin.sum_univ_three]
  norm_num at h0 h1 h2 ⊢
  nlinarith

#print axioms unitaryThree_row_fourthPotential_ge_one_third
#print axioms unitaryThree_fourthPotential_ge_one

end D5.S3.Quantum.Tomography.UnitaryThreeFramePotential

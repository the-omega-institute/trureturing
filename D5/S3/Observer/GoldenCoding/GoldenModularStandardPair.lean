/- GID: D5/S3/Observer/GoldenCoding/GoldenModularStandardPair
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/GoldenModularStandardPair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden modular step squares to a positive definite unimodular operator. -/

import Mathlib

/- Library-search audit trail (2026-09-01):
   * The atom ledger and formalization receipts contain no coverage for the
     golden modular standard pair, and current-tree searches found no theorem
     with this matrix and conclusion.
   * Neighboring golden-coding modules and the pending GoldenHyperbolicAxis
     lane use a different Fibonacci matrix convention, so they do not supply
     the required square.
   * Pinned Mathlib supplies `Matrix.posDef_iff_dotProduct_mulVec`,
     `Matrix.det_fin_two`, `Matrix.trace_fin_two`, and the golden-ratio
     identities used below, but no exact theorem for this standard pair. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix

namespace D5.S3.Observer.GoldenCoding.GoldenModularStandardPair

/-- The one-step golden modular matrix in the convention of the standard pair. -/
def goldenModularStep : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 1]

/-- The modular operator of the golden standard pair. -/
def goldenModularOperator : Matrix (Fin 2) (Fin 2) ℝ := goldenModularStep ^ 2

theorem goldenModularStep_sq :
    goldenModularStep ^ 2 = !![1, 1; 1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [goldenModularStep, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem goldenModularOperator_eq :
    goldenModularOperator = !![1, 1; 1, 2] := by
  exact goldenModularStep_sq

theorem goldenModularOperator_det : goldenModularOperator.det = 1 := by
  rw [goldenModularOperator_eq, Matrix.det_fin_two]
  norm_num

theorem goldenModularOperator_trace : Matrix.trace goldenModularOperator = 3 := by
  rw [goldenModularOperator_eq, Matrix.trace_fin_two]
  norm_num

theorem goldenModularOperator_posDef : goldenModularOperator.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · rw [goldenModularOperator_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply]
  · intro x hx
    rw [goldenModularOperator_eq]
    norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    by_cases h1 : x 1 = 0
    · have h0 : x 0 ≠ 0 := by
        intro hx0
        apply hx
        funext i
        fin_cases i <;> assumption
      have h0sq : 0 < x 0 ^ 2 := sq_pos_of_ne_zero h0
      rw [h1]
      nlinarith
    · have h1sq : 0 < x 1 ^ 2 := sq_pos_of_ne_zero h1
      have hsum : 0 ≤ (x 0 + x 1) ^ 2 := sq_nonneg (x 0 + x 1)
      nlinarith

theorem goldenModularWitness_e0 :
    ![1, 0] ⬝ᵥ (goldenModularOperator *ᵥ ![1, 0]) = (1 : ℝ) := by
  rw [goldenModularOperator_eq]
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_two]

theorem goldenModularWitness_antiDiagonal :
    ![1, -1] ⬝ᵥ (goldenModularOperator *ᵥ ![1, -1]) = (1 : ℝ) := by
  rw [goldenModularOperator_eq]
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_two]

theorem goldenRatio_sq_mul_inv_sq :
    Real.goldenRatio ^ 2 * Real.goldenRatio⁻¹ ^ 2 = 1 := by
  rw [← mul_pow]
  rw [mul_inv_cancel₀ (ne_of_gt Real.goldenRatio_pos)]
  norm_num

theorem goldenRatio_sq_add_inv_sq :
    Real.goldenRatio ^ 2 + Real.goldenRatio⁻¹ ^ 2 = 3 := by
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenRatio_sq, Real.goldenConj_sq,
    Real.goldenRatio_add_goldenConj]

/-- The golden first phase gives a finite-dimensional modular standard pair:
its modular operator is the explicit positive definite unimodular matrix with
trace three, and its two reciprocal golden scales have product one and sum
three. The two displayed test directions witness the quadratic form directly. -/
theorem golden_modular_standard_pair :
    goldenModularStep ^ 2 = !![1, 1; 1, 2] /\
      goldenModularOperator.det = 1 /\
      Matrix.trace goldenModularOperator = 3 /\
      goldenModularOperator.PosDef /\
      ![1, 0] ⬝ᵥ (goldenModularOperator *ᵥ ![1, 0]) = (1 : ℝ) /\
      ![1, -1] ⬝ᵥ (goldenModularOperator *ᵥ ![1, -1]) = (1 : ℝ) /\
      Real.goldenRatio ^ 2 * Real.goldenRatio⁻¹ ^ 2 = 1 /\
      Real.goldenRatio ^ 2 + Real.goldenRatio⁻¹ ^ 2 = 3 := by
  exact ⟨goldenModularStep_sq, goldenModularOperator_det,
    goldenModularOperator_trace, goldenModularOperator_posDef,
    goldenModularWitness_e0, goldenModularWitness_antiDiagonal,
    goldenRatio_sq_mul_inv_sq, goldenRatio_sq_add_inv_sq⟩

#print axioms golden_modular_standard_pair

end D5.S3.Observer.GoldenCoding.GoldenModularStandardPair

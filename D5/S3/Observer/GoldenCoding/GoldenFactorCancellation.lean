/- GID: D5/S3/Observer/GoldenCoding/GoldenFactorCancellation
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/GoldenFactorCancellation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden-normalized real involutions multiply to the standard complex structure. -/

import Mathlib

/-!
Library-search audit trail (2026-09-03):
* D5 name searches for golden factor cancellation, real polarization, and
  standard complex structures found no whole-statement owner.
* D5 body-shape searches for the two source matrices `!![1, 2; 2, -1]`
  and `!![2, -1; -1, -2]` found no hit.
* Pinned Mathlib searches by the same matrix bodies and by factorization of a
  complex structure into involutions found no exact theorem. Mathlib supplies
  the matrix arithmetic and the defining radical formula for `goldenRatio`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix

namespace D5.S3.Observer.GoldenCoding.GoldenFactorCancellation

/-- Two real involutions whose normalization is determined by the golden
ratio multiply to the standard complex structure. Their reverse product has
the opposite orientation, while the completed structure squares to `-I`. -/
theorem golden_factor_cancellation :
    let S : Matrix (Fin 2) (Fin 2) Real :=
      (2 * Real.goldenRatio - 1)⁻¹ • !![1, 2; 2, -1]
    let C : Matrix (Fin 2) (Fin 2) Real :=
      (2 * Real.goldenRatio - 1)⁻¹ • !![2, -1; -1, -2]
    let J : Matrix (Fin 2) (Fin 2) Real := !![0, -1; 1, 0]
    S * S = 1 ∧
      C * C = 1 ∧
      S * C = J ∧
      C * S = -J ∧
      J * J = -1 := by
  have hnormalization : 2 * Real.goldenRatio - 1 = Real.sqrt 5 := by
    rw [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 by rfl]
    ring
  have hsqrtSquare : Real.sqrt 5 ^ 2 = (5 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hsqrtNonzero : Real.sqrt 5 ≠ 0 := by positivity
  dsimp only
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hnormalization] <;>
      field_simp <;> nlinarith
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hnormalization] <;>
      field_simp <;> nlinarith
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hnormalization] <;>
      field_simp <;> nlinarith
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hnormalization] <;>
      field_simp <;> nlinarith
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

#print axioms golden_factor_cancellation

end D5.S3.Observer.GoldenCoding.GoldenFactorCancellation

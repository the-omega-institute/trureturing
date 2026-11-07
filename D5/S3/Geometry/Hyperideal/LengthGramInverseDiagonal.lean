/- GID: D5/S3/Geometry/Hyperideal/LengthGramInverseDiagonal
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LengthGramInverseDiagonal
   mirror-E: none(waiver:exact-inverse-diagonal-positivity)
   anchors: []
   utility: none
   digest: Strict positivity of every diagonal entry of the inverse six-length Gram matrix. -/

import D5.S3.Geometry.Hyperideal.LengthGramBody
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! Strict positivity of every diagonal entry of the inverse six-length Gram matrix.

The GID is `D5/S3/Geometry/Hyperideal/LengthGramInverseDiagonal`; its mirror is
`D5/B/S3/Geometry/Hyperideal/LengthGramInverseDiagonal` and it has no E mirror
under the exact inverse-diagonal-positivity waiver. -/

noncomputable section
open scoped BigOperators Matrix
open D5.S3.Geometry.Hyperideal.LengthGramBody
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.LengthGramInverseDiagonal

private theorem tri_minor_negative (u v w : ℝ)
    (hu : 1 < u) (hv : 1 < v) (hw : 1 < w) :
    (!![1, -u, -v; -u, 1, -w; -v, -w, 1] : Matrix (Fin 3) (Fin 3) ℝ).det < 0 := by
  norm_num [Matrix.det_fin_three, Matrix.det_fin_two, Matrix.det_fin_one,
    Matrix.det_fin_zero]
  have huv : 0 < u * v := mul_pos (lt_trans (by norm_num) hu) (lt_trans (by norm_num) hv)
  have huw : 0 < u * w := mul_pos (lt_trans (by norm_num) hu) (lt_trans (by norm_num) hw)
  have hvw : 0 < v * w := mul_pos (lt_trans (by norm_num) hv) (lt_trans (by norm_num) hw)
  nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg w]

private theorem principal_minor_negative (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) (i : Fin 4) :
    (Matrix.adjugate (lengthGram l)) i i < 0 := by
  have hcosh (k : Fin 6) : 1 < Real.cosh (l k) :=
    Real.one_lt_cosh.mpr (ne_of_gt (hl k))
  have htri (u v w : ℝ) (hu : 1 < u) (hv : 1 < v) (hw : 1 < w) :=
    tri_minor_negative u v w hu hv hw
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  fin_cases i
  · convert (htri (Real.cosh (l 3)) (Real.cosh (l 4)) (Real.cosh (l 5))
      (hcosh 3) (hcosh 4) (hcosh 5)) using 1 <;>
      norm_num [lengthGram, Matrix.submatrix_apply, Fin.succAbove, Fin.reduceEq,
        Fin.reduceFinMk, Matrix.det_fin_three, Matrix.det_fin_two, Matrix.det_fin_one,
        Matrix.det_fin_zero] <;> ring
  · convert (htri (Real.cosh (l 1)) (Real.cosh (l 2)) (Real.cosh (l 3))
      (hcosh 1) (hcosh 2) (hcosh 3)) using 1 <;>
      norm_num [lengthGram, Matrix.submatrix_apply, Fin.succAbove, Fin.reduceEq,
        Fin.reduceFinMk, Matrix.det_fin_three, Matrix.det_fin_two, Matrix.det_fin_one,
        Matrix.det_fin_zero] <;> ring
  · convert (htri (Real.cosh (l 0)) (Real.cosh (l 2)) (Real.cosh (l 4))
      (hcosh 0) (hcosh 2) (hcosh 4)) using 1 <;>
      norm_num [lengthGram, Matrix.submatrix_apply, Fin.succAbove, Fin.reduceEq,
        Fin.reduceFinMk, Matrix.det_fin_three, Matrix.det_fin_two, Matrix.det_fin_one,
        Matrix.det_fin_zero] <;> ring
  · convert (htri (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 5))
      (hcosh 0) (hcosh 1) (hcosh 5)) using 1 <;>
      norm_num [lengthGram, Matrix.submatrix_apply, Fin.succAbove, Fin.reduceEq,
        Fin.reduceFinMk, Matrix.det_fin_three, Matrix.det_fin_two, Matrix.det_fin_one,
        Matrix.det_fin_zero] <;> ring

theorem inverse_diagonal_pos (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) (i : Fin 4) :
    (lengthGram l)⁻¹ i i > 0 := by
  have hminor := principal_minor_negative l hl i
  rw [Matrix.inv_def]
  change Ring.inverse ((lengthGram l).det) * (Matrix.adjugate (lengthGram l) i i) > 0
  rw [Ring.inverse_eq_inv]
  have hinv : ((lengthGram l).det)⁻¹ < 0 := (inv_neg'').2 hdet
  exact mul_pos_of_neg_of_neg hinv hminor

#print axioms inverse_diagonal_pos
end D5.S3.Geometry.Hyperideal.LengthGramInverseDiagonal

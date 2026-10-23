/- GID: D5/S3/Geometry/Hyperideal/SixIndependentLengthRemainder
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/SixIndependentLengthRemainder
   mirror-E: none(waiver:exact-six-length-remainder)
   anchors: []
   utility: none
   digest: Exact determinant remainder for the six-independent-length character coordinates. -/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.SixIndependentLengthRemainder

def gram (r o A B xi zeta : Real) : Matrix (Fin 4) (Fin 4) Real :=
  !![ 1 - r, -A - B, 0, -xi + zeta;
      -A - B, 1 - o, -xi - zeta, 0;
      0, -xi - zeta, 1 + r, -A + B;
      -xi + zeta, 0, -A + B, 1 + o ]

def L (r o A B : Real) : Real :=
  (A + B) ^ 2 - (r - 1) * (o - 1)

def M (r o A B : Real) : Real :=
  (r + 1) * (o + 1) - (A - B) ^ 2

def Xi (r o A B xi zeta : Real) : Real :=
  2 * (r * o - 1 - A ^ 2 + B ^ 2) * xi ^ 2
    + 2 * (r * o - 1 + A ^ 2 - B ^ 2) * zeta ^ 2
    + 4 * (r - o) * xi * zeta
    + (xi ^ 2 - zeta ^ 2) ^ 2

theorem determinant_remainder_identity (r o A B xi zeta : Real) :
    (gram r o A B xi zeta).det = -L r o A B * M r o A B + Xi r o A B xi zeta := by
  norm_num (config := {decide := true}) [L, M, Xi, gram,
    Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.det_fin_two, Matrix.det_fin_one, Matrix.det_fin_zero,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Matrix.of_apply,
    Matrix.cons_val_zero', Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ,
    Matrix.vecHead, Matrix.vecTail, Fin.succAbove, Fin.reduceEq, Fin.reduceFinMk,
    Fin.castSucc, Fin.castAdd, Fin.succ, Fin.val_zero, Fin.val_succ,
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.castLE, Fin.cast]
  ring

theorem determinant_negative_iff (r o A B xi zeta : Real) :
    Iff ((gram r o A B xi zeta).det < 0)
      (Xi r o A B xi zeta < L r o A B * M r o A B) := by
  rw [determinant_remainder_identity]
  constructor <;> intro h <;> linarith

#print axioms determinant_remainder_identity
#print axioms determinant_negative_iff

end D5.S3.Geometry.Hyperideal.SixIndependentLengthRemainder

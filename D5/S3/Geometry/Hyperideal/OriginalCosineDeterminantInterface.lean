/- GID: D5/S3/Geometry/Hyperideal/OriginalCosineDeterminantInterface
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/OriginalCosineDeterminantInterface
   mirror-E: none(waiver:original-cosine-determinant-interface)
   anchors: []
   utility: none
   digest: The original six-cosh cosine numerator and determinant identity for one target edge. -/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface

def gram (r a b o c d : Real) : Matrix (Fin 4) (Fin 4) Real :=
  !![ 1, -r, -a, -b;
      -r, 1, -d, -c;
      -a, -d, 1, -o;
      -b, -c, -o, 1 ]

def D1 (r a d : Real) : Real := r ^ 2 + a ^ 2 + d ^ 2 + 2 * r * a * d - 1

def D2 (r b c : Real) : Real := r ^ 2 + b ^ 2 + c ^ 2 + 2 * r * b * c - 1

def N (r a b o c d : Real) : Real :=
  a * b + c * d + r * a * c + r * b * d - (r ^ 2 - 1) * o

private theorem determinant_identity (r a b o c d : Real) :
    D1 r a d * D2 r b c - N r a b o c d ^ 2 =
      -(r ^ 2 - 1) * (gram r a b o c d).det := by
  norm_num [D1, D2, N, gram,
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

private theorem positive_factors {r a b o c d : Real}
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (ho : 1 < o)
    (hc : 1 < c) (hd : 1 < d) :
    0 < D1 r a d ∧ 0 < D2 r b c := by
  have hrad : 0 < r * a * d :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hrbc : 0 < r * b * c :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  constructor <;> dsimp [D1, D2] <;> nlinarith [sq_nonneg r, sq_nonneg a,
    sq_nonneg b, sq_nonneg c, sq_nonneg d]

theorem original_cosine_interface (r a b o c d : Real)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (ho : 1 < o)
    (hc : 1 < c) (hd : 1 < d) :
    (0 < D1 r a d ∧ 0 < D2 r b c) ∧
      (D1 r a d * D2 r b c - N r a b o c d ^ 2 =
        -(r ^ 2 - 1) * (gram r a b o c d).det) ∧
      ((gram r a b o c d).det < 0 ↔
        0 < D1 r a d * D2 r b c - N r a b o c d ^ 2) := by
  have hpos := positive_factors hr ha hb ho hc hd
  have hid := determinant_identity r a b o c d
  have hcoef : 0 < r ^ 2 - 1 := by nlinarith
  have hcrit : (gram r a b o c d).det < 0 ↔
      0 < D1 r a d * D2 r b c - N r a b o c d ^ 2 := by
    rw [hid]
    constructor <;> intro h <;> nlinarith
  exact ⟨hpos, hid, hcrit⟩

#print axioms original_cosine_interface

end D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface

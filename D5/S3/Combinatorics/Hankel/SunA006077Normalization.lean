/- GID: D5/S3/Combinatorics/Hankel/SunA006077Normalization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hankel/SunA006077Normalization
   mirror-E: none(waiver:integral-determinant-row-normalization)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic]
   utility: none
   digest: Powers of six and odd integral quotients of the two multinomial Hankel families. -/

import D5.S3.Combinatorics.Hankel.SunA006077Binary
import D5.S3.Combinatorics.Hankel.SunA006077Arithmetic

/-! Integral row division and reduction to the two binary determinant families. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Hankel.SunA006077

open Matrix Finset

/-- The unshifted determinant with all rows except the first divided by six. -/
def d (m : ℕ) : ℤ :=
  (Matrix.of fun i j : Fin (m+1) => if i.val=0 then c j.val else (q (i.val+j.val) : ℤ)).det

/-- The shifted determinant with every row divided by six. -/
def e (m : ℕ) : ℤ :=
  (Matrix.of fun i j : Fin m => (q (i.val+j.val+1) : ℤ)).det

/-- The unshifted row normalization is an exact integral factorization. -/
theorem D_normalization (m : ℕ) : D (m+1)=6^m*d m := by
  let A : Matrix (Fin (m+1)) (Fin (m+1)) ℤ :=
    Matrix.of fun i j => if i.val=0 then c j.val else (q (i.val+j.val) : ℤ)
  let f : Fin (m+1) → ℤ := fun i => if i.val=0 then 1 else 6
  have hm : (Matrix.of fun i j : Fin (m+1) => c (i.val+j.val)) =
      Matrix.of (fun i j => f i * A i j) := by
    ext i j
    by_cases hi : i.val=0
    · simp [f,A,hi]
    · simp only [Matrix.of_apply,f,A,hi,ite_false]
      exact c_six _ (by omega)
  have hp : (∏ i : Fin (m+1), f i)=(6 : ℤ)^m := by
    rw [Fin.prod_univ_succ]
    simp [f]
  unfold D d
  rw [hm,Matrix.det_mul_column,hp]

/-- The shifted row normalization is an exact integral factorization. -/
theorem E_normalization (m : ℕ) : E m=6^m*e m := by
  have hm : (Matrix.of fun i j : Fin m => c (i.val+j.val+1)) =
      Matrix.of (fun i j : Fin m => (6 : ℤ)*(q (i.val+j.val+1) : ℤ)) := by
    ext i j
    exact c_six _ (by omega)
  unfold E e
  rw [hm,Matrix.det_mul_column]
  simp

private theorem q_mod_two (r : ℕ) (hr : 0 < r) : (q r : ZMod 2)=epsilon r := by
  classical
  by_cases h : ∃ k : ℕ, r=2^k
  · simp only [epsilon,h,ite_true]
    exact ZMod.natCast_eq_one_iff_odd.mpr ((q_odd_iff r hr).mpr h)
  · simp only [epsilon,h,ite_false]
    by_contra hz
    exact h ((q_odd_iff r hr).mp (ZMod.natCast_ne_zero_iff_odd.mp hz))

private theorem c_mod_two (r : ℕ) (hr : 0 < r) : (c r : ZMod 2)=0 := by
  rw [c_six r hr]
  push_cast
  norm_num

/-- Both integral quotient determinants are odd at every size. -/
theorem normalized_odd (m : ℕ) : Odd (d m) ∧ Odd (e m) := by
  have he : (e m : ZMod 2)=S m := by
    unfold e S
    rw [Int.cast_det]
    congr 1
    ext i j
    simp only [Matrix.map_apply,Matrix.of_apply,Int.cast_natCast]
    exact q_mod_two _ (by omega)
  have hd : (d m : ZMod 2)=T m := by
    let M : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod 2) :=
      Matrix.of fun i j => if i.val=0 then (if j.val=0 then 1 else 0)
        else epsilon (i.val+j.val)
    have hm : (d m : ZMod 2)=M.det := by
      unfold d
      rw [Int.cast_det]
      congr 1
      ext i j
      by_cases hi : i.val=0
      · by_cases hj : j.val=0
        · simp [M,hi,hj,c]
        · simp only [Matrix.map_apply,Matrix.of_apply,hi,hj,ite_true,ite_false]
          exact c_mod_two _ (by omega)
      · simp only [Matrix.map_apply,Matrix.of_apply,hi,ite_false,M,Int.cast_natCast]
        exact q_mod_two _ (by omega)
    rw [hm,Matrix.det_succ_row_zero,sum_eq_single 0]
    · have hminor : M.submatrix Fin.succ Fin.succ =
          Matrix.of (fun i j : Fin m => epsilon (i.val+j.val+2)) := by
        ext i j
        simp only [M,Matrix.submatrix_apply,Matrix.of_apply,Fin.val_succ]
        simp [show i.val+1 ≠ 0 by omega,show i.val+1+(j.val+1)=i.val+j.val+2 by omega]
      simp only [M,Matrix.of_apply,Fin.val_zero,ite_true,pow_zero,one_mul,
        Fin.succAbove_zero,hminor]
      rfl
    · intro j _ hj
      have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp [M,hjv]
    · simp
  constructor
  · exact ZMod.intCast_eq_one_iff_odd.mp (hd.trans (rueppel_determinants m).2)
  · exact ZMod.intCast_eq_one_iff_odd.mp (he.trans (rueppel_determinants m).1)

end D5.S3.Combinatorics.Hankel.SunA006077

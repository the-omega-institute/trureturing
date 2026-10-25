import D5.S3.Geometry.Hyperideal.CFMPOriginalInternalNormals435Transient
import D5.S3.Geometry.Hyperideal.CFMPFrameMotion435Transient
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Temporary cofactor calculation for the original affine coefficient chart. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody

namespace CFMPCoefficientAreaDeterminant435Transient

abbrev V := Fin 3 → ℝ
abbrev W := Fin 4 → ℝ
abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ

def rows (a v w t : W) : M4 := ![a,v,w,t]
def lift (x : V) : W := ![x 0,x 1,x 2,1-x 0-x 1-x 2]
def tangent (v : V) : W := ![v 0,v 1,v 2,-v 0-v 1-v 2]
def covector (A : V) (c : ℝ) : W := ![A 0-c,A 1-c,A 2-c,-c]
def raw (M : M4) (A : V) (c : ℝ) : W :=
  let z := M⁻¹ *ᵥ covector A c
  ![z 0,z 1,z 2,-z 3]

theorem coefficient_det (x v w : V) (t : W) :
    (rows (lift x) (tangent v) (tangent w) t).det =
      -dotProduct t (covector (v ⨯₃ w) (dotProduct (v ⨯₃ w) x)) := by
  rw [Matrix.det_succ_row_zero (n := 3)]
  norm_num [Matrix.det_fin_three,Matrix.submatrix,rows,lift,tangent,covector,
    dotProduct,Fin.sum_univ_succ,cross_apply,Matrix.of_apply,
    Matrix.cons_val_zero',Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_succ,
    Matrix.vecHead,Matrix.vecTail,Fin.succAbove,Fin.reduceEq,Fin.reduceFinMk,
    Fin.castSucc,Fin.castAdd,Fin.succ,Fin.val_zero,Fin.val_succ,
    Nat.succ_eq_add_one,Nat.reduceAdd,Fin.castLE,Fin.cast]
  ring

theorem rows_mul (a v w t : W) (M : M4) :
    rows (a ᵥ* M) (v ᵥ* M) (w ᵥ* M) (t ᵥ* M) = rows a v w t * M := by
  ext i j
  fin_cases i <;> rfl

theorem pair_raw (M : M4) (hM : M.det ≠ 0) (a : W) (A : V) (c : ℝ) :
    lorentz (a ᵥ* M) (raw M A c) = dotProduct a (covector A c) := by
  calc
    _ = dotProduct (a ᵥ* M) (M⁻¹ *ᵥ covector A c) := by
      simp [raw,lorentz,dotProduct,Fin.sum_univ_four]
    _ = dotProduct a ((M*M⁻¹) *ᵥ covector A c) := by
      simp only [Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul]
    _ = _ := by
      rw [Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM),Matrix.one_mulVec]

theorem actual_frame_det (M : M4) (hM : M.det ≠ 0) (x v w : V) (Y : W) :
    (rows ((lift x) ᵥ* M) ((tangent v) ᵥ* M) ((tangent w) ᵥ* M) Y).det =
      -M.det * lorentz Y (raw M (v ⨯₃ w) (dotProduct (v ⨯₃ w) x)) := by
  have hcancel : (Y ᵥ* M⁻¹) ᵥ* M = Y := by
    rw [Matrix.vecMul_vecMul,Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM),
      Matrix.vecMul_one]
  have hr := rows_mul (lift x) (tangent v) (tangent w) (Y ᵥ* M⁻¹) M
  rw [hcancel] at hr
  rw [hr,Matrix.det_mul,coefficient_det]
  have hp := pair_raw M hM (Y ᵥ* M⁻¹) (v ⨯₃ w) (dotProduct (v ⨯₃ w) x)
  rw [hcancel] at hp
  rw [← hp]
  ring

theorem actual_frame_normal_det (M : M4) (hM : M.det ≠ 0) (x v w : V) :
    let R := raw M (v ⨯₃ w) (dotProduct (v ⨯₃ w) x)
    (rows ((lift x) ᵥ* M) ((tangent v) ᵥ* M) ((tangent w) ᵥ* M) R).det =
      -M.det * lorentz R R := by
  exact actual_frame_det M hM x v w _

#print axioms actual_frame_normal_det
end CFMPCoefficientAreaDeterminant435Transient

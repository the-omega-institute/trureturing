import D5.S3.Geometry.Hyperideal.LengthGramSideTrace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.CrossProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
namespace CFMPOriginalCellsOrientation435Transient

def edges (l : Fin 6 → ℝ) (n : Fin 20) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => vertices l n j.succ i.castSucc - vertices l n 0 i.castSucc

def determinantValue (l : Fin 6 → ℝ) : Fin 20 → ℝ :=
  let c := fun k : Fin 6 => Real.cosh (l k)
  ![(c 0+c 1+c 2-1)/(4*(c 0+1)*(c 1+1)*(c 2+1)),
    -((c 0+c 5+c 4-1)/(4*(c 0+1)*(c 5+1)*(c 4+1))),
    (c 1+c 5+c 3-1)/(4*(c 1+1)*(c 5+1)*(c 3+1)),
    -((c 2+c 4+c 3-1)/(4*(c 2+1)*(c 4+1)*(c 3+1))),
    -((c 5-1)/(4*(c 5+1)*(c 3+1))),
    -(c 5*(c 3-1)/(4*(c 5+1)*(c 3+1))),
    -((c 5*c 4+c 3)/(4*(c 5+1)*(c 3+1)*(c 4+1))),
    -((c 4-1)/(4*(c 5+1)*(c 4+1))),
    (c 1-1)/(4*(c 1+1)*(c 3+1)),
    c 1*(c 3-1)/(4*(c 1+1)*(c 3+1)),
    (c 1*c 2+c 3)/(4*(c 1+1)*(c 3+1)*(c 2+1)),
    (c 2-1)/(4*(c 1+1)*(c 2+1)),
    -((c 0-1)/(4*(c 0+1)*(c 4+1))),
    -(c 0*(c 4-1)/(4*(c 0+1)*(c 4+1))),
    -((c 0*c 2+c 4)/(4*(c 0+1)*(c 4+1)*(c 2+1))),
    -((c 2-1)/(4*(c 0+1)*(c 2+1))),
    (c 0-1)/(4*(c 0+1)*(c 5+1)),
    c 0*(c 5-1)/(4*(c 0+1)*(c 5+1)),
    (c 0*c 1+c 5)/(4*(c 0+1)*(c 5+1)*(c 1+1)),
    (c 1-1)/(4*(c 0+1)*(c 1+1))]

set_option maxHeartbeats 2000000 in
theorem exact_original_determinant (l : Fin 6 → ℝ) (n : Fin 20) :
    (edges l n).det = determinantValue l n := by
  have h (k : Fin 6) : 1 + Real.cosh (l k) ≠ 0 := by positivity
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  fin_cases n <;>
    simp [edges,determinantValue,vertices,endpoint,barycenter,lengthGram,
      Matrix.det_fin_three] <;>
    field_simp <;> ring


def sign (n : Fin 20) : ℝ :=
  ![1,-1,1,-1,-1,-1,-1,-1,1,1,1,1,-1,-1,-1,-1,1,1,1,1] n

theorem signed_det_positive (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) (n : Fin 20) :
    0 < sign n * (edges l n).det := by
  have hc (k : Fin 6) : 1 < Real.cosh (l k) := Real.one_lt_cosh.mpr (hl k).ne'
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have h5 := hc 5
  have hm0 : 0 < Real.cosh (l 0)-1 := by linarith
  have hm1 : 0 < Real.cosh (l 1)-1 := by linarith
  have hm2 : 0 < Real.cosh (l 2)-1 := by linarith
  have hm3 : 0 < Real.cosh (l 3)-1 := by linarith
  have hm4 : 0 < Real.cosh (l 4)-1 := by linarith
  have hm5 : 0 < Real.cosh (l 5)-1 := by linarith
  have hs0 : 0 < Real.cosh (l 0)+Real.cosh (l 1)+Real.cosh (l 2)-1 := by linarith
  have hs1 : 0 < Real.cosh (l 0)+Real.cosh (l 5)+Real.cosh (l 4)-1 := by linarith
  have hs2 : 0 < Real.cosh (l 1)+Real.cosh (l 5)+Real.cosh (l 3)-1 := by linarith
  have hs3 : 0 < Real.cosh (l 2)+Real.cosh (l 4)+Real.cosh (l 3)-1 := by linarith
  rw [exact_original_determinant]
  fin_cases n <;> norm_num [sign,determinantValue] <;> positivity

theorem abs_det_eq_signed (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) (n : Fin 20) :
    |(edges l n).det| = sign n * (edges l n).det := by
  have h := signed_det_positive l hl n
  have hs : sign n = 1 ∨ sign n = -1 := by
    fin_cases n <;> simp [sign]
  rcases hs with hs | hs
  · have hd : 0 < (edges l n).det := by simpa only [hs,one_mul] using h
    simpa only [hs,one_mul] using (abs_of_pos hd)
  · have hd : (edges l n).det < 0 := by
      rw [hs,neg_one_mul] at h
      linarith
    simpa only [hs,neg_one_mul] using (abs_of_neg hd)

theorem abs_div_det_eq_sign (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) (n : Fin 20) :
    |(edges l n).det| / (edges l n).det = sign n := by
  rw [abs_det_eq_signed l hl n]
  have hd : (edges l n).det ≠ 0 := by
    intro h
    have h' := signed_det_positive l hl n
    simp [h] at h'
  exact mul_div_cancel_right₀ _ hd

def normal (i : Fin 3) : Fin 3 → ℝ :=
  ![![-1,0,0], ![0,-1,0], ![0,0,-1]] i

def area (B : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) : Fin 3 → ℝ :=
  ![-(crossProduct (B.col 1) (B.col 2)),
    crossProduct (B.col 0) (B.col 2),
    -(crossProduct (B.col 0) (B.col 1))] i

theorem adjugate_face (B : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    B.adjugate.transpose.mulVec (normal i) = area B i := by
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [normal,area,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
      Matrix.adjugate_fin_three,Matrix.transpose_apply,cross_apply,Matrix.col_apply] <;> ring

def coefficient (B : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) : Fin 3 → ℝ :=
  |B.det| • (B⁻¹).transpose.mulVec (normal i)

theorem coefficient_eq_area (B : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    coefficient B i = (|B.det| / B.det) • area B i := by
  simp only [coefficient,Matrix.inv_def,Ring.inverse_eq_inv,Matrix.transpose_smul,
    Matrix.smul_mulVec,smul_smul,adjugate_face,div_eq_mul_inv]

theorem area_dot_opposite (B : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    dotProduct (area B i) (B.col i) = -B.det := by
  fin_cases i <;>
    simp [area,cross_apply,dotProduct,Fin.sum_univ_three,Matrix.col_apply,
      Matrix.det_fin_three] <;> ring

theorem coefficient_dot_opposite (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hd : B.det ≠ 0) (i : Fin 3) :
    dotProduct (coefficient B i) (B.col i) = -|B.det| := by
  rw [coefficient_eq_area,smul_dotProduct,area_dot_opposite]
  simp [smul_eq_mul,div_eq_mul_inv,mul_assoc,hd]


theorem coefficient_dot_mulVec (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hd : B.det ≠ 0) (i : Fin 3) (u : Fin 3 → ℝ) :
    dotProduct (coefficient B i) (B.mulVec u) = -|B.det| * u i := by
  rw [coefficient,smul_dotProduct,dotProduct_comm,
    Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),Matrix.one_mulVec]
  fin_cases i <;> simp [normal,dotProduct,Fin.sum_univ_three,smul_eq_mul]

theorem coefficient_nonpositive (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hd : B.det ≠ 0) (i : Fin 3) (u : Fin 3 → ℝ) (hu : 0 ≤ u i) :
    dotProduct (coefficient B i) (B.mulVec u) ≤ 0 := by
  rw [coefficient_dot_mulVec B hd i u]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg _)) hu

end CFMPOriginalCellsOrientation435Transient

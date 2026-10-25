import D5.S3.Geometry.Hyperideal.LengthGramBody
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Compactness.Compact
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Matrix.Normed

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Matrix Topology ContDiff Matrix.Norms.Elementwise
namespace CFMPAnchoredSmoothFrame435Transient
abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ
abbrev L := Fin 6 → ℝ
def J : Mat := Matrix.diagonal ![1,1,1,-1]
def r0 (H : Mat) := H 0 0
def c00 (H : Mat) := Real.sqrt (r0 H)
def c10 (H : Mat) := H 1 0 / c00 H
def c20 (H : Mat) := H 2 0 / c00 H
def c30 (H : Mat) := H 3 0 / c00 H
def r1 (H : Mat) := H 1 1 - c10 H ^ 2
def c11 (H : Mat) := Real.sqrt (r1 H)
def c21 (H : Mat) := (H 2 1 - c20 H * c10 H) / c11 H
def c31 (H : Mat) := (H 3 1 - c30 H * c10 H) / c11 H
def r2 (H : Mat) := H 2 2 - c20 H ^ 2 - c21 H ^ 2
def c22 (H : Mat) := Real.sqrt (r2 H)
def c32 (H : Mat) := (H 3 2 - c30 H * c20 H - c31 H * c21 H) / c22 H
def r3 (H : Mat) := -H 3 3 + c30 H ^ 2 + c31 H ^ 2 + c32 H ^ 2
def c33 (H : Mat) := Real.sqrt (r3 H)
def C (H : Mat) : Mat :=
  !![c00 H,0,0,0; c10 H,c11 H,0,0; c20 H,c21 H,c22 H,0;
    c30 H,c31 H,c32 H,c33 H]
def good (H : Mat) : Prop := 0 < r0 H ∧ 0 < r1 H ∧ 0 < r2 H ∧ 0 < r3 H

theorem base : C J = 1 ∧ good J := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [C,c00,c10,c20,c30,c11,c21,c31,c22,c32,c33,r0,r1,r2,r3,J]
  · norm_num [good,c00,c10,c20,c30,c11,c21,c31,c22,c32,c33,r0,r1,r2,r3,J]

def T (a b c d e f g h i j : ℝ) : Mat :=
  !![a,0,0,0; b,c,0,0; d,e,f,0; g,h,i,j]

theorem product_00 (a b c d e f g h i j : ℝ) :
    (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 0 0 =
      a*a := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply, Fin.sum_univ_four]
  norm_num [T]
  <;> ring

theorem product_01 (a b c d e f g h i j : ℝ) :
    (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 0 1 =
      a*b := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply, Fin.sum_univ_four]
  norm_num [T]
  <;> ring

theorem product_02 (a b c d e f g h i j : ℝ) :
    (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 0 2 =
      a*d := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply, Fin.sum_univ_four]
  norm_num [T]
  <;> ring

theorem product_03 (a b c d e f g h i j : ℝ) :
    (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 0 3 =
      a*g := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply, Fin.sum_univ_four]
  norm_num [T]
  <;> ring

theorem product_10 (a b c d e f g h i j : ℝ) :
    (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 1 0 =
      b*a := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply, Fin.sum_univ_four]
  norm_num [T]
  <;> ring

theorem product_11 (a b c d e f g h i j : ℝ) :
    (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 1 1 =
      b*b+c*c := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply, Fin.sum_univ_four]
  norm_num [T]
  <;> ring

theorem product_12 (a b c d e f g h i j : ℝ) :
    (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 1 2 =
      b*d+c*e := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply, Fin.sum_univ_four]
  norm_num [T]
  <;> ring

theorem product_13 (a b c d e f g h i j : ℝ) :
    (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 1 3 =
      b*g+c*h := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply, Fin.sum_univ_four]
  norm_num [T]
  <;> ring

theorem product_20 (a b c d e f g h i j : ℝ) :
    (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 2 0 =
      d*a := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply, Fin.sum_univ_four]
  norm_num [T]
  <;> ring

theorem product_21 (a b c d e f g h i j : ℝ) :
    (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 2 1 =
      d*b+e*c := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply, Fin.sum_univ_four]
  norm_num [T]
  <;> ring

theorem product_22 (a b c d e f g h i j : ℝ) :
    (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 2 2 =
      d*d+e*e+f*f := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply, Fin.sum_univ_four]
  norm_num [T]
  <;> ring

theorem product_23 (a b c d e f g h i j : ℝ) :
    (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 2 3 =
      d*g+e*h+f*i := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply, Fin.sum_univ_four]
  norm_num [T]
  <;> ring

theorem product_30 (a b c d e f g h i j : ℝ) :
    (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 3 0 =
      g*a := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply, Fin.sum_univ_four]
  norm_num [T]
  <;> ring

theorem product_31 (a b c d e f g h i j : ℝ) :
    (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 3 1 =
      g*b+h*c := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply, Fin.sum_univ_four]
  norm_num [T]
  <;> ring

theorem product_32 (a b c d e f g h i j : ℝ) :
    (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 3 2 =
      g*d+h*e+i*f := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply, Fin.sum_univ_four]
  norm_num [T]
  <;> ring

theorem product_33 (a b c d e f g h i j : ℝ) :
    (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 3 3 =
      g*g+h*h+i*i-j*j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply, Fin.sum_univ_four]
  norm_num [T]
  <;> ring

theorem triangular_factor (a b c d e f g h i j : ℝ) (H : Mat)
    (hs : H.transpose = H)
    (s0 : a^2 = H 0 0) (s1 : b^2+c^2 = H 1 1)
    (s2 : d^2+e^2+f^2 = H 2 2) (s3 : g^2+h^2+i^2-j^2 = H 3 3)
    (q10 : b*a = H 1 0) (q20 : d*a = H 2 0) (q30 : g*a = H 3 0)
    (q21 : d*b+e*c = H 2 1) (q31 : g*b+h*c = H 3 1)
    (q32 : g*d+h*e+i*f = H 3 2) :
    T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose = H := by
  have sym (i j : Fin 4) : H j i = H i j := congrArg (fun A : Mat => A i j) hs
  have t01 := sym 0 1
  have t02 := sym 0 2
  have t03 := sym 0 3
  have t12 := sym 1 2
  have t13 := sym 1 3
  have t23 := sym 2 3
  apply Matrix.ext
  intro u v
  fin_cases u <;> fin_cases v
  · change (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 0 0 = H 0 0
    rw [product_00]
    simpa only [← pow_two] using s0
  · change (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 0 1 = H 0 1
    rw [product_01]
    simpa only [mul_comm] using q10.trans t01
  · change (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 0 2 = H 0 2
    rw [product_02]
    simpa only [mul_comm] using q20.trans t02
  · change (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 0 3 = H 0 3
    rw [product_03]
    simpa only [mul_comm] using q30.trans t03
  · change (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 1 0 = H 1 0
    rw [product_10]
    exact q10
  · change (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 1 1 = H 1 1
    rw [product_11]
    simpa only [← pow_two] using s1
  · change (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 1 2 = H 1 2
    rw [product_12]
    simpa only [mul_comm] using q21.trans t12
  · change (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 1 3 = H 1 3
    rw [product_13]
    simpa only [mul_comm] using q31.trans t13
  · change (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 2 0 = H 2 0
    rw [product_20]
    exact q20
  · change (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 2 1 = H 2 1
    rw [product_21]
    exact q21
  · change (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 2 2 = H 2 2
    rw [product_22]
    simpa only [← pow_two] using s2
  · change (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 2 3 = H 2 3
    rw [product_23]
    simpa only [mul_comm] using q32.trans t23
  · change (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 3 0 = H 3 0
    rw [product_30]
    exact q30
  · change (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 3 1 = H 3 1
    rw [product_31]
    exact q31
  · change (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 3 2 = H 3 2
    rw [product_32]
    exact q32
  · change (T a b c d e f g h i j * J * (T a b c d e f g h i j).transpose) 3 3 = H 3 3
    rw [product_33]
    simpa only [← pow_two] using s3

theorem factor (H : Mat) (hs : H.transpose = H) (hg : good H) :
    C H * J * (C H).transpose = H := by
  rcases hg with ⟨h0,h1,h2,h3⟩
  have n0 : c00 H ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h0)
  have n1 : c11 H ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h1)
  have n2 : c22 H ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h2)
  have s0 : c00 H ^ 2 = H 0 0 := Real.sq_sqrt h0.le
  have s1 : c11 H ^ 2 = H 1 1 - c10 H ^ 2 := Real.sq_sqrt h1.le
  have s2 : c22 H ^ 2 = H 2 2 - c20 H ^ 2 - c21 H ^ 2 := Real.sq_sqrt h2.le
  have s3 : c33 H ^ 2 = -H 3 3 + c30 H ^ 2 + c31 H ^ 2 + c32 H ^ 2 :=
    Real.sq_sqrt h3.le
  have q10 : c10 H * c00 H = H 1 0 := div_mul_cancel₀ _ n0
  have q20 : c20 H * c00 H = H 2 0 := div_mul_cancel₀ _ n0
  have q30 : c30 H * c00 H = H 3 0 := div_mul_cancel₀ _ n0
  have q21 : c21 H * c11 H = H 2 1 - c20 H * c10 H := div_mul_cancel₀ _ n1
  have q31 : c31 H * c11 H = H 3 1 - c30 H * c10 H := div_mul_cancel₀ _ n1
  have q32 : c32 H * c22 H = H 3 2 - c30 H * c20 H - c31 H * c21 H :=
    div_mul_cancel₀ _ n2
  apply triangular_factor (c00 H) (c10 H) (c11 H) (c20 H) (c21 H) (c22 H)
    (c30 H) (c31 H) (c32 H) (c33 H) H hs s0
  · linarith [s1]
  · linarith [s2]
  · linarith [s3]
  · exact q10
  · exact q20
  · exact q30
  · linarith [q21]
  · linarith [q31]
  · linarith [q32]

theorem smooth_data (H : Mat) (hg : good H) :
    ContDiffAt ℝ ∞ C H ∧ ContDiffAt ℝ ∞ r0 H ∧
      ContDiffAt ℝ ∞ r1 H ∧ ContDiffAt ℝ ∞ r2 H ∧ ContDiffAt ℝ ∞ r3 H := by
  rcases hg with ⟨h0,h1,h2,h3⟩
  have e (i j : Fin 4) : ContDiffAt ℝ ∞ (fun A : Mat => A i j) H := by fun_prop
  have hr0 : ContDiffAt ℝ ∞ r0 H := e 0 0
  have h00 : ContDiffAt ℝ ∞ c00 H := hr0.sqrt (ne_of_gt h0)
  have h10 : ContDiffAt ℝ ∞ c10 H := (e 1 0).div h00 (ne_of_gt (Real.sqrt_pos.mpr h0))
  have h20 : ContDiffAt ℝ ∞ c20 H := (e 2 0).div h00 (ne_of_gt (Real.sqrt_pos.mpr h0))
  have h30 : ContDiffAt ℝ ∞ c30 H := (e 3 0).div h00 (ne_of_gt (Real.sqrt_pos.mpr h0))
  have hr1 : ContDiffAt ℝ ∞ r1 H := (e 1 1).sub (h10.pow 2)
  have h11 : ContDiffAt ℝ ∞ c11 H := hr1.sqrt (ne_of_gt h1)
  have h21 : ContDiffAt ℝ ∞ c21 H :=
    ((e 2 1).sub (h20.mul h10)).div h11 (ne_of_gt (Real.sqrt_pos.mpr h1))
  have h31 : ContDiffAt ℝ ∞ c31 H :=
    ((e 3 1).sub (h30.mul h10)).div h11 (ne_of_gt (Real.sqrt_pos.mpr h1))
  have hr2 : ContDiffAt ℝ ∞ r2 H := ((e 2 2).sub (h20.pow 2)).sub (h21.pow 2)
  have h22 : ContDiffAt ℝ ∞ c22 H := hr2.sqrt (ne_of_gt h2)
  have h32 : ContDiffAt ℝ ∞ c32 H :=
    (((e 3 2).sub (h30.mul h20)).sub (h31.mul h21)).div h22
      (ne_of_gt (Real.sqrt_pos.mpr h2))
  have hr3 : ContDiffAt ℝ ∞ r3 H :=
    (((e 3 3).neg.add (h30.pow 2)).add (h31.pow 2)).add (h32.pow 2)
  have h33 : ContDiffAt ℝ ∞ c33 H := hr3.sqrt (ne_of_gt h3)
  refine ⟨?_,hr0,hr1,hr2,hr3⟩
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp only [C,Matrix.of_apply,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] <;>
    first | exact h00 | exact h10 | exact h20 | exact h30 | exact h11 | exact h21 |
      exact h31 | exact h22 | exact h32 | exact h33 | exact contDiffAt_const

theorem good_open : IsOpen {H : Mat | good H} := by
  rw [isOpen_iff_mem_nhds]
  intro H hg
  rcases smooth_data H hg with ⟨_,h0,h1,h2,h3⟩
  rcases hg with ⟨g0,g1,g2,g3⟩
  have a0 := continuousAt_const.eventually_lt h0.continuousAt g0
  have a1 := continuousAt_const.eventually_lt h1.continuousAt g1
  have a2 := continuousAt_const.eventually_lt h2.continuousAt g2
  have a3 := continuousAt_const.eventually_lt h3.continuousAt g3
  filter_upwards [a0,a1,a2,a3] with A a b c d using ⟨a,b,c,d⟩


theorem det_C_positive (A : Mat) (hg : good A) : 0 < (C A).det := by
  have ht : (C A).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;> norm_num [Fin.lt_def] at hij
    all_goals rfl
  rw [Matrix.det_of_isLowerTriangular _ ht]
  apply Finset.prod_pos
  intro i _
  fin_cases i
  · exact Real.sqrt_pos.mpr hg.1
  · exact Real.sqrt_pos.mpr hg.2.1
  · exact Real.sqrt_pos.mpr hg.2.2.1
  · exact Real.sqrt_pos.mpr hg.2.2.2

open D5.S3.Geometry.Hyperideal.LengthGramBody

def H (M0 : Mat) (l : L) : Mat := M0⁻¹ * lengthGram l * M0⁻¹.transpose

def frame (M0 : Mat) (l : L) : Mat := M0 * C (H M0 l)

theorem normalized_base (M0 : Mat) (hm : M0.det ≠ 0) (l0 : L)
    (hbase : M0 * J * M0.transpose = lengthGram l0) : H M0 l0 = J := by
  unfold H
  rw [← hbase]
  calc
    _ = (M0⁻¹ * M0) * J * (M0⁻¹ * M0).transpose := by
      simp only [Matrix.transpose_mul,Matrix.mul_assoc]
    _ = J := by rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hm)]; simp

theorem anchored (M0 : Mat) (hm : M0.det ≠ 0) (l0 : L)
    (hbase : M0 * J * M0.transpose = lengthGram l0) : frame M0 l0 = M0 := by
  rw [frame,normalized_base M0 hm l0 hbase,base.1,Matrix.mul_one]

theorem gram_symmetric (l : L) : (lengthGram l).transpose = lengthGram l := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem H_symmetric (M0 : Mat) (l : L) : (H M0 l).transpose = H M0 l := by
  simp only [H,Matrix.transpose_mul,Matrix.transpose_transpose,gram_symmetric,Matrix.mul_assoc]

theorem frame_gram (M0 : Mat) (hm : M0.det ≠ 0) (l : L) (hg : good (H M0 l)) :
    frame M0 l * J * (frame M0 l).transpose = lengthGram l := by
  have hf := factor (H M0 l) (H_symmetric M0 l) hg
  unfold frame
  rw [Matrix.transpose_mul]
  calc
    _ = M0 * (C (H M0 l) * J * (C (H M0 l)).transpose) * M0.transpose := by
      simp only [Matrix.mul_assoc]
    _ = M0 * H M0 l * M0.transpose := by rw [hf]
    _ = lengthGram l := by
      unfold H
      calc
        _ = (M0 * M0⁻¹) * lengthGram l * (M0 * M0⁻¹).transpose := by
          simp only [Matrix.transpose_mul,Matrix.mul_assoc]
        _ = lengthGram l := by
          rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hm)]; simp

theorem smooth_H (M0 : Mat) : ContDiff ℝ ∞ (H M0) := by
  have hcoord (k : Fin 6) : ContDiff ℝ ∞ (fun l : L => l k) := by fun_prop
  have hg : ContDiff ℝ ∞ lengthGram := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;> first
      | exact contDiff_const
      | exact (Real.contDiff_cosh.comp (hcoord 0)).neg
      | exact (Real.contDiff_cosh.comp (hcoord 1)).neg
      | exact (Real.contDiff_cosh.comp (hcoord 2)).neg
      | exact (Real.contDiff_cosh.comp (hcoord 3)).neg
      | exact (Real.contDiff_cosh.comp (hcoord 4)).neg
      | exact (Real.contDiff_cosh.comp (hcoord 5)).neg

  have hleft : ContDiff ℝ ∞ (fun l => M0⁻¹ * lengthGram l) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    change ContDiff ℝ ∞ (fun l => ∑ k, M0⁻¹ i k * lengthGram l k j)
    apply ContDiff.sum
    intro k _
    exact contDiff_const.mul ((contDiff_pi.mp ((contDiff_pi.mp hg) k)) j)
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ ∞ (fun l => ∑ k, (M0⁻¹ * lengthGram l) i k * M0⁻¹.transpose k j)
  apply ContDiff.sum
  intro k _
  exact ((contDiff_pi.mp ((contDiff_pi.mp hleft) i)) k).mul contDiff_const

theorem smooth_frame (M0 : Mat) (l : L) (hg : good (H M0 l)) :
    ContDiffAt ℝ ∞ (frame M0) l := by
  have hc := (smooth_data _ hg).1.comp l (smooth_H M0).contDiffAt
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  change ContDiffAt ℝ ∞ (fun x => ∑ k, M0 i k * C (H M0 x) k j) l
  apply ContDiffAt.sum
  intro k _
  exact contDiffAt_const.mul ((contDiffAt_pi.mp ((contDiffAt_pi.mp hc) k)) j)

theorem frame_det_nonzero (M0 : Mat) (hm : M0.det ≠ 0) (l : L)
    (hg : good (H M0 l)) : (frame M0 l).det ≠ 0 := by
  rw [frame,Matrix.det_mul]
  exact mul_ne_zero hm (ne_of_gt (det_C_positive _ hg))

theorem local_original_frame (M0 : Mat) (hm : M0.det ≠ 0) (l0 : L)
    (hl : ∀ i, 0 < l0 i) (hbase : M0 * J * M0.transpose = lengthGram l0) :
    ∃ V : Set L, IsOpen V ∧ l0 ∈ V ∧ (∀ l ∈ V, ∀ i, 0 < l i) ∧
      frame M0 l0 = M0 ∧ ContDiffOn ℝ ∞ (frame M0) V ∧
      (∀ l ∈ V, frame M0 l * J * (frame M0 l).transpose = lengthGram l) := by
  let V : Set L := {l | good (H M0 l)} ∩ {l | ∀ i, 0 < l i}
  have hv : IsOpen V :=
    (good_open.preimage (smooth_H M0).continuous).inter
      (by simpa only [Set.ofPred_forall] using
        (isOpen_iInter_of_finite fun i : Fin 6 => isOpen_lt
          (continuous_const : Continuous (fun _ : L => (0:ℝ))) (continuous_apply i)))
  refine ⟨V,hv,?_,fun l h => h.2,anchored M0 hm l0 hbase,?_,?_⟩
  · exact ⟨by change good (H M0 l0); rw [normalized_base M0 hm l0 hbase]; exact base.2,hl⟩
  · intro l h
    exact (smooth_frame M0 l h.1).contDiffWithinAt
  · intro l h
    exact frame_gram M0 hm l h.1
end CFMPAnchoredSmoothFrame435Transient

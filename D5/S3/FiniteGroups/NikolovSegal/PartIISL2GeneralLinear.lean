/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIISL2GeneralLinear
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIISL2GeneralLinear
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: General-linear conjugation and semilinear SL2 scalar products. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIISL2Semilinear
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
set_option autoImplicit false
namespace NikolovSegal.PartIIA1RootSupply
open Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

private def glAction (A : Matrix.GeneralLinearGroup (Fin 2) F) (g : SL(2,F)) : SL(2,F) :=
  ⟨(↑A : Matrix (Fin 2) (Fin 2) F) * g.val * ((↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F),by
    rw [Matrix.det_mul,Matrix.det_mul,g.property,mul_one,← Matrix.det_mul,A.mul_inv,Matrix.det_one]⟩

/-- Actual conjugation by an arbitrary invertible 2x2 matrix, restricted to SL2. -/
def generalLinearAut (A : Matrix.GeneralLinearGroup (Fin 2) F) : MulAut SL(2,F) where
  toFun := glAction A
  invFun := glAction A⁻¹
  left_inv g := by
    apply Subtype.ext
    change ((↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((↑A : Matrix (Fin 2) (Fin 2) F)*g.val*(↑A⁻¹ : Matrix (Fin 2) (Fin 2) F)) * (↑(A⁻¹)⁻¹ : Matrix (Fin 2) (Fin 2) F) = g.val
    rw [inv_inv]
    simp only [← mul_assoc,A.inv_mul,one_mul]
    rw [mul_assoc,A.inv_mul,mul_one]
  right_inv g := by
    apply Subtype.ext
    change (↑A : Matrix (Fin 2) (Fin 2) F) *
      (((↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)*g.val*(↑(A⁻¹)⁻¹ : Matrix (Fin 2) (Fin 2) F)) * (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) = g.val
    rw [inv_inv]
    simp only [← mul_assoc,A.mul_inv,one_mul]
    rw [mul_assoc,A.mul_inv,mul_one]
  map_mul' g h := by
    apply Subtype.ext
    change (↑A : Matrix (Fin 2) (Fin 2) F)*(g.val*h.val)*(↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) =
      ((↑A : Matrix (Fin 2) (Fin 2) F)*g.val*(↑A⁻¹ : Matrix (Fin 2) (Fin 2) F))*((↑A : Matrix (Fin 2) (Fin 2) F)*h.val*(↑A⁻¹ : Matrix (Fin 2) (Fin 2) F))
    simp only [mul_assoc]
    rw [← mul_assoc (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) (↑A : Matrix (Fin 2) (Fin 2) F),A.inv_mul,one_mul]

private def diagonalGL (a : Fˣ) : Matrix.GeneralLinearGroup (Fin 2) F where
  val := !![(a:F),0;0,1]
  inv := !![(↑a⁻¹:F),0;0,1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two]

private theorem generalLinear_diagonal (a : Fˣ) : generalLinearAut (diagonalGL a) = diagonalAut a := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  change (glAction (diagonalGL a) g).val = !![g 0 0,(a:F)*g 0 1;(↑a⁻¹:F)*g 1 0,g 1 1]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [glAction,diagonalGL,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  all_goals field_simp

private theorem generalLinear_mul (A B : Matrix.GeneralLinearGroup (Fin 2) F) :
    generalLinearAut (A*B) = generalLinearAut A * generalLinearAut B := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  change (↑(A*B):Matrix (Fin 2) (Fin 2) F)*g.val*(↑(A*B)⁻¹ : Matrix (Fin 2) (Fin 2) F) =
    (↑A : Matrix (Fin 2) (Fin 2) F)*((↑B : Matrix (Fin 2) (Fin 2) F)*g.val*(↑B⁻¹ : Matrix (Fin 2) (Fin 2) F))*(↑A⁻¹ : Matrix (Fin 2) (Fin 2) F)
  simp only [Units.val_mul,mul_inv_rev,mul_assoc]

private theorem generalLinear_SL (g : SL(2,F)) : generalLinearAut (toGL g) = MulAut.conj g := by
  apply MulEquiv.ext
  intro h
  apply Subtype.ext
  rfl

private theorem gl_normalization (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    ∃ g : SL(2,F), generalLinearAut A =
      MulAut.conj g * diagonalAut (Matrix.GeneralLinearGroup.det A) := by
  let a := Matrix.GeneralLinearGroup.det A
  let B := A*(diagonalGL a)⁻¹
  have hdet : Matrix.GeneralLinearGroup.det B = 1 := by
    simp only [B,map_mul,map_inv]
    have hd : Matrix.GeneralLinearGroup.det (diagonalGL a) = a := by
      apply Units.ext
      simp [Matrix.GeneralLinearGroup.det,diagonalGL,Matrix.det_fin_two]
    rw [hd]
    exact mul_inv_cancel a
  let g : SL(2,F) := ⟨(↑B : Matrix (Fin 2) (Fin 2) F),congrArg Units.val hdet⟩
  have hg : toGL g = B := Units.ext rfl
  have hA : A = toGL g * diagonalGL a := by
    rw [hg]
    dsimp only [B]
    group
  refine ⟨g,?_⟩
  calc
    generalLinearAut A = generalLinearAut (toGL g*diagonalGL a) := congrArg generalLinearAut hA
    _ = MulAut.conj g*diagonalAut a := by
      rw [generalLinear_mul,generalLinear_SL,generalLinear_diagonal]

/-- Actual full scalar PRODUCT for every prescribed semilinear GL2 matrix
conjugation, with exact q/e, one correction tuple before all targets and
uniform explicit field/length bounds. No root laws or coverage are premises. -/
theorem actual_GL2_semilinear_scalar_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (A : Fin (4*M) → Matrix.GeneralLinearGroup (Fin 2) F)
    (phi : Fin (4*M) → RingAut F) (e : Fin (4*M) → ℕ) :
    PartIIScalarProductInput q (4*M)
      (fun j => generalLinearAut (A j)*fieldAut (phi j)) e := by
  classical
  choose g hg using fun j => gl_normalization (A j)
  have hbeta : (fun j => generalLinearAut (A j)*fieldAut (phi j)) =
      (fun j => MulAut.conj (g j)*semilinearAut (Matrix.GeneralLinearGroup.det (A j)) (phi j)) := by
    funext j
    rw [hg]
    rfl
  rw [hbeta]
  exact actual_inner_semilinear_SL2_scalar_product hq hM hF _ phi g e
end NikolovSegal.PartIIA1RootSupply

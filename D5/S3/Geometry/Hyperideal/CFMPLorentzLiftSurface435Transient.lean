import D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody

namespace CFMPLorentzLiftSurface435Transient

abbrev V := Fin 3 → ℝ
abbrev W := Fin 4 → ℝ

def coordinateLift (p : V) : W :=
  ![p 0 / p 2, p 1 / p 2,
    ((p 0)^2 + (p 1)^2 + (p 2)^2 - 1) / (2 * p 2),
    ((p 0)^2 + (p 1)^2 + (p 2)^2 + 1) / (2 * p 2)]

-- Exact substitution into the original native-space lift.
example (p : D5.S3.Geometry.HyperbolicUpperHalfSpace.HyperbolicThreeSpace) :
    coordinateLift ![p.coordinates.val.fst.re, p.coordinates.val.fst.im,
      D5.S3.Geometry.HyperbolicUpperHalfSpace.height p.coordinates] =
      D5.S3.Geometry.Hyperideal.LengthGramMetricSegments.lift p := by
  rfl

def liftMatrix (p : V) : Matrix (Fin 4) (Fin 3) ℝ :=
  !![(p 2)⁻¹, 0, -p 0 / (p 2)^2;
     0, (p 2)⁻¹, -p 1 / (p 2)^2;
     p 0 / p 2, p 1 / p 2,
       ((p 2)^2 - (p 0)^2 - (p 1)^2 + 1) / (2 * (p 2)^2);
     p 0 / p 2, p 1 / p 2,
       ((p 2)^2 - (p 0)^2 - (p 1)^2 - 1) / (2 * (p 2)^2)]

theorem coordinateLift_hasFDerivAt (p : V) (hp : p 2 ≠ 0) :
    HasFDerivAt coordinateLift (liftMatrix p).mulVecLin.toContinuousLinearMap p := by
  have h (i : Fin 3) : HasFDerivAt (fun w : V => w i)
      (ContinuousLinearMap.proj i) p := (ContinuousLinearMap.proj i : V →L[ℝ] ℝ).hasFDerivAt
  have hi := (hasDerivAt_inv hp).comp_hasFDerivAt p (h 2)
  have hQ := ((h 0).mul (h 0)).add ((h 1).mul (h 1)) |>.add ((h 2).mul (h 2))
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert (h 0).mul hi using 1
    · funext w
      simp [coordinateLift, div_eq_mul_inv]
    · ext w
      simp [liftMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, smul_eq_mul]
      <;> field_simp [hp]
      <;> ring
  · convert (h 1).mul hi using 1
    · funext w
      simp [coordinateLift, div_eq_mul_inv]
    · ext w
      simp [liftMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, smul_eq_mul]
      <;> field_simp [hp]
      <;> ring
  · convert ((hQ.sub_const 1).mul hi).const_mul (1 / 2 : ℝ) using 1
    · funext w
      simp [coordinateLift, div_eq_mul_inv, pow_two]
      <;> ring
    · ext w
      simp [liftMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, smul_eq_mul]
      <;> field_simp [hp]
      <;> ring
  · convert ((hQ.add_const 1).mul hi).const_mul (1 / 2 : ℝ) using 1
    · funext w
      simp [coordinateLift, div_eq_mul_inv, pow_two]
      <;> ring
    · ext w
      simp [liftMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, smul_eq_mul]
      <;> field_simp [hp]
      <;> ring

-- This is a coordinate identity for the derivative of the existing lift,
-- not an assumption of a Riemannian/native measure identification.
theorem liftMatrix_lorentz (p v w : V) (hp : p 2 ≠ 0) :
    lorentz ((liftMatrix p).mulVec v) ((liftMatrix p).mulVec w) =
      dotProduct v w / (p 2)^2 := by
  simp [liftMatrix, lorentz, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four, Fin.sum_univ_three]
  <;> field_simp [hp]
  <;> ring

-- A smooth coordinate identity through a Lorentz isometry transfers
-- the actual coordinate Gram form; its hypotheses still need exact instantiation.
theorem equal_gram_of_lift_identity
    (p q : V) (hp : p 2 ≠ 0) (hq : q 2 ≠ 0)
    (A B : Matrix (Fin 3) (Fin 2) ℝ) (R : W →ₗ[ℝ] W)
    (hR : ∀ v w, lorentz (R v) (R w) = lorentz v w)
    (hAB : ∀ j, (liftMatrix p).mulVec (A.col j) =
      R ((liftMatrix q).mulVec (B.col j))) (i j : Fin 2) :
    dotProduct (A.col i) (A.col j) / (p 2)^2 =
      dotProduct (B.col i) (B.col j) / (q 2)^2 := by
  rw [← liftMatrix_lorentz p _ _ hp,
    hAB i, hAB j, hR, liftMatrix_lorentz q _ _ hq]

end CFMPLorentzLiftSurface435Transient

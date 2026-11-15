/- GID: D5/S3/Quantum/TensorNetworks/InteriorPolynomialRealCalculus
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/InteriorPolynomialRealCalculus
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.PDeriv]
   utility: none
   digest: Ordinary real slice derivatives of independent-trial polynomials. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Determinant

/-! Real Fréchet derivatives for polynomial slices with fixed target coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.Quantum.TensorNetworks.InteriorPolynomialRealCalculus

open MvPolynomial
open scoped Matrix

def slice {κ : Type*} (θ : κ → ℝ) (z : ℂ) : Fin 2 ⊕ κ → ℝ :=
  Sum.elim ![z.re, z.im] θ

def sliceDerivative {κ : Type*} (F : MvPolynomial (Fin 2 ⊕ κ) ℝ)
    (θ : κ → ℝ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  eval (slice θ z) (pderiv (Sum.inl 0) F) • Complex.reCLM +
  eval (slice θ z) (pderiv (Sum.inl 1) F) • Complex.imCLM

/-- The target coordinates are constants; only the two trial coordinates vary. -/
theorem hasFDerivAt_slice {κ : Type*} (F : MvPolynomial (Fin 2 ⊕ κ) ℝ)
    (θ : κ → ℝ) (z : ℂ) :
    HasFDerivAt (fun w : ℂ => eval (slice θ w) F) (sliceDerivative F θ z) z := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => simpa [sliceDerivative] using (hasFDerivAt_const (𝕜 := ℝ) a z)
  | add F G hF hG =>
      convert! (HasFDerivAt.add (𝕜 := ℝ) hF hG) using 1
      · ext w; simp
      · ext w; simp [sliceDerivative]; ring
  | mul_X F i hF =>
      have hX : HasFDerivAt (fun w : ℂ => slice θ w i)
          (sliceDerivative (X i) θ z) z := by
        rcases i with i | i
        · fin_cases i
          · convert! Complex.reCLM.hasFDerivAt (x := z) using 1 <;>
              (try ext w) <;> simp [sliceDerivative,slice,pderiv_X,Complex.reCLM_apply]
          · convert! Complex.imCLM.hasFDerivAt (x := z) using 1 <;>
              (try ext w) <;> simp [sliceDerivative,slice,pderiv_X,Complex.imCLM_apply]
        · simpa [sliceDerivative, slice, pderiv_X] using (hasFDerivAt_const (𝕜 := ℝ) (θ i) z)
      convert! (HasFDerivAt.mul (𝕜 := ℝ) hF hX) using 1
      · ext w; simp
      · ext w
        simp [sliceDerivative, pderiv_mul, smul_eq_mul]
        ring

/-- Columns are the inputs 1,I; rows are the real and imaginary outputs. -/
theorem real_det (D : ℂ →L[ℝ] ℂ) :
    LinearMap.det D.toLinearMap =
      (D 1).re * (D Complex.I).im - (D Complex.I).re * (D 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  rw [Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply]
  change (D (Complex.basisOneI 0)).re * (D (Complex.basisOneI 1)).im -
    (D (Complex.basisOneI 1)).re * (D (Complex.basisOneI 0)).im = _
  simp only [Complex.coe_basisOneI,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one]

def trialJacobian {κ : Type*} (F H : MvPolynomial (Fin 2 ⊕ κ) ℝ) :
    MvPolynomial (Fin 2 ⊕ κ) ℝ :=
  pderiv (Sum.inl 0) F * pderiv (Sum.inl 1) H -
    pderiv (Sum.inl 1) F * pderiv (Sum.inl 0) H

/-- At a common root, clearing multiplies the two derivative rows by its factors. -/
theorem cleared_jacobian {κ : Type*} (F H : MvPolynomial (Fin 2 ⊕ κ) ℝ)
    (θ : κ → ℝ) (z : ℂ) (f : ℂ → ℂ) (D : ℂ →L[ℝ] ℂ)
    (c e : ℂ → ℝ) (hf : f z = 0) (hd : HasFDerivAt f D z)
    (hc : DifferentiableAt ℝ c z) (he : DifferentiableAt ℝ e z)
    (hF : (fun w => eval (slice θ w) F) =ᶠ[nhds z] fun w => c w * (f w).re)
    (hH : (fun w => eval (slice θ w) H) =ᶠ[nhds z] fun w => e w * (f w).im) :
    eval (slice θ z) (trialJacobian F H) = c z * e z * LinearMap.det D.toLinearMap := by
  have hleft := hc.hasFDerivAt.mul (Complex.reCLM.hasFDerivAt.comp z hd)
  have hright := he.hasFDerivAt.mul (Complex.imCLM.hasFDerivAt.comp z hd)
  have hL := (hasFDerivAt_slice F θ z).unique (hleft.congr_of_eventuallyEq hF)
  have hR := (hasFDerivAt_slice H θ z).unique (hright.congr_of_eventuallyEq hH)
  have hL1 := congrArg (fun T : ℂ →L[ℝ] ℝ => T 1) hL
  have hLI := congrArg (fun T : ℂ →L[ℝ] ℝ => T Complex.I) hL
  have hR1 := congrArg (fun T : ℂ →L[ℝ] ℝ => T 1) hR
  have hRI := congrArg (fun T : ℂ →L[ℝ] ℝ => T Complex.I) hR
  simp [sliceDerivative, hf] at hL1 hLI hR1 hRI
  simp only [trialJacobian, map_sub, map_mul, real_det]
  rw [hL1, hLI, hR1, hRI]
  ring

end D5.S3.Quantum.TensorNetworks.InteriorPolynomialRealCalculus

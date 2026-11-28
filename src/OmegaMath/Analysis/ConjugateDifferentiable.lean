import OmegaBuild.Commands
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! Omega original.
Constancy from simultaneous complex differentiability of a function and its conjugate. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ComplexConjugate

namespace Omega

/-- A complex-differentiable function with complex-differentiable conjugate is constant. -/
theorem constant_of_differentiable_conj {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ (fun z => conj (f z))) (x y : ℂ) :
    f x = f y := by
  apply is_const_of_deriv_eq_zero hf _ x y
  intro z
  let g : ℂ → ℂ := fun w => conj (f w)
  let J := Complex.conjCLE.toContinuousLinearMap
  have hf' := (hf z).hasFDerivAt.restrictScalars (𝕜 := ℝ)
  have hg' := (hg z).hasFDerivAt.restrictScalars (𝕜 := ℝ)
  have hj := J.hasFDerivAt.comp z hf'
  have he := hg'.fderiv.symm.trans hj.fderiv
  have at_one := DFunLike.congr_fun he (1 : ℂ)
  have at_I := DFunLike.congr_fun he Complex.I
  change fderiv ℂ g z 1 = conj (fderiv ℂ f z 1) at at_one
  change fderiv ℂ g z Complex.I = conj (fderiv ℂ f z Complex.I) at at_I
  rw [show Complex.I = Complex.I • (1 : ℂ) by simp, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_I, at_one] at at_I
  have hzero : conj (fderiv ℂ f z 1) = 0 := by
    apply (mul_eq_zero.mp (_ : (2 * Complex.I) * conj (fderiv ℂ f z 1) = 0)).resolve_left
      (by simp [Complex.I_ne_zero])
    linear_combination at_I
  simpa only [map_eq_zero, deriv] using hzero

end Omega

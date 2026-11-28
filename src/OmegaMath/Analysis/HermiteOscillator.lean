import OmegaBuild.Commands
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
Omega original.

Hermite eigenfunctions of the displaced oscillator in its physical coordinate.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Polynomial

namespace Omega.Analysis.HermiteOscillator

private def numberPolynomial (p : Polynomial ℤ) : Polynomial ℤ :=
  X * derivative p - derivative (derivative p)

private def raisePolynomial (p : Polynomial ℤ) : Polynomial ℤ :=
  X * p - derivative p

private theorem number_raise (p : Polynomial ℤ) :
    numberPolynomial (raisePolynomial p) =
      raisePolynomial (numberPolynomial p) + raisePolynomial p := by
  simp only [numberPolynomial, raisePolynomial, derivative_sub, derivative_mul,
    derivative_X, one_mul, derivative_add]
  ring

private theorem number_hermite (n : ℕ) :
    numberPolynomial (hermite n) = n • hermite n := by
  induction n with
  | zero => simp [numberPolynomial, hermite_zero]
  | succ n ih =>
    change numberPolynomial (hermite (n + 1)) = (n + 1) • hermite (n + 1)
    rw [show hermite (n + 1) = raisePolynomial (hermite n) from hermite_succ n,
      number_raise, ih, add_nsmul]
    simp only [raisePolynomial, nsmul_eq_mul, derivative_natCast_mul]
    ring

private def hermiteReal (n : ℕ) : Polynomial ℝ := (hermite n).map (Int.castRingHom ℝ)

private theorem number_hermiteReal (n : ℕ) :
    X * derivative (hermiteReal n) - derivative (derivative (hermiteReal n)) =
      (n : ℝ) • hermiteReal n := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℝ)) (number_hermite n)
  simpa [numberPolynomial, hermiteReal, Polynomial.derivative_map, nsmul_eq_mul,
    Polynomial.smul_eq_C_mul, Polynomial.C_eq_natCast] using h

private def shiftedDerivative (p : Polynomial ℝ) : Polynomial ℝ :=
  derivative p - C (1 / 2) * X * p

private def withGaussian (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  p.eval x * Real.exp (-(x ^ 2 / 4))

private theorem withGaussian_hasDeriv (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (withGaussian p) (withGaussian (shiftedDerivative p) x) x := by
  have hg := (((hasDerivAt_id' x).pow 2).div_const 4).neg.exp
  have h := (Polynomial.hasDerivAt p x).fun_mul hg
  convert h using 1
  · rfl
  · simp [withGaussian, shiftedDerivative, Pi.pow_apply]
    ring

private theorem gaussian_eq (n : ℕ) (x : ℝ) :
    -2 * withGaussian (shiftedDerivative (shiftedDerivative (hermiteReal n))) x +
      x ^ 2 / 2 * withGaussian (hermiteReal n) x =
      (2 * (n : ℝ) + 1) * withGaussian (hermiteReal n) x := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval x) (number_hermiteReal n)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_smul, smul_eq_mul] at h
  simp only [withGaussian, shiftedDerivative, derivative_sub, derivative_mul,
    derivative_C, derivative_X, zero_mul, zero_add,
    eval_mul, eval_sub, eval_X, eval_C, eval_add, eval_one]
  linear_combination 2 * Real.exp (-(x ^ 2 / 4)) * h

/-- Hermite mode in the rescaled and translated coordinate of the quadratic potential. -/
def mode (q k : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  withGaussian (hermiteReal n) (Real.sqrt (2 * q) * (x + k / q))

theorem mode_oscillator (q k : ℝ) (hq : 0 < q) (n : ℕ) :
    mode q k n ≠ 0 ∧
      ∀ x : ℝ, -deriv (deriv (mode q k n)) x + (k + q * x) ^ 2 * mode q k n x =
          (2 * (n : ℝ) + 1) * q * mode q k n x := by
  let s := Real.sqrt (2 * q)
  let z : ℝ → ℝ := fun x => s * (x + k / q)
  have hs : 0 < s := by unfold s; positivity
  have hs₂ : s ^ 2 = 2 * q := Real.sq_sqrt (by positivity)
  have hz (x : ℝ) : HasDerivAt z s x := by
    simpa [z] using (HasDerivAt.const_mul s ((hasDerivAt_id' x).add_const (k / q)))
  have hcompose (p : Polynomial ℝ) :
      deriv (fun x => withGaussian p (z x)) =
        fun x => withGaussian (shiftedDerivative p) (z x) * s := by
    funext x
    exact ((withGaussian_hasDeriv p (z x)).comp x (hz x)).deriv
  refine ⟨?_, ?_⟩
  · intro h
    have hzer : (hermiteReal n) = 0 := by
      apply Polynomial.funext
      intro y
      have hzy : z (y / s - k / q) = y := by simp [z, mul_div_cancel₀, hs.ne']
      have hh := congrFun h (y / s - k / q)
      change withGaussian (hermiteReal n) (z (y / s - k / q)) = 0 at hh
      rw [hzy, withGaussian, mul_eq_zero, or_iff_left (Real.exp_ne_zero _)] at hh
      simpa using hh
    exact ((hermite_monic n).map (Int.castRingHom ℝ)).ne_zero hzer
  · intro x
    change -deriv (deriv (fun x => withGaussian (hermiteReal n) (z x))) x +
        (k + q * x) ^ 2 * withGaussian (hermiteReal n) (z x) = _
    unfold mode
    change _ = (2 * (n : ℝ) + 1) * q * withGaussian (hermiteReal n) (z x)
    rw [hcompose]
    have hd := ((withGaussian_hasDeriv (shiftedDerivative (hermiteReal n)) (z x)).comp x
      (hz x)).mul_const s
    have hd' := hd.deriv
    simp only [Function.comp_apply] at hd'
    rw [hd']
    have hx : (k + q * x) ^ 2 = q * (z x) ^ 2 / 2 := by
      rw [show z x = s * (x + k / q) from rfl, mul_pow, hs₂]
      field_simp [hq.ne']
      ring
    rw [hx, mul_assoc, ← pow_two, hs₂]
    linear_combination q * gaussian_eq n (z x)

end Omega.Analysis.HermiteOscillator

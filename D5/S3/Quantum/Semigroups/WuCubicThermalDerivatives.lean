import D5.S0.Certificates.BoxCover.RationalIntervalExpression
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Topology

namespace D5.S3.Quantum.Semigroups.WuCubicThermalDerivatives

open D5.S0.Certificates.BoxCover.RationalIntervalExpression

/-- The first derivative formula holds near `x` by `HasDerivAt.fun_mul`. -/
theorem hasDerivAt_deriv_mul {f g f₁ g₁ : ℝ → ℝ} {x f₂ g₂ : ℝ}
    (hf : ∀ᶠ y in 𝓝 x, HasDerivAt f (f₁ y) y)
    (hg : ∀ᶠ y in 𝓝 x, HasDerivAt g (g₁ y) y)
    (hf₁ : HasDerivAt f₁ f₂ x) (hg₁ : HasDerivAt g₁ g₂ x) :
    HasDerivAt (deriv (fun y => f y * g y))
      (f₂ * g x + 2 * f₁ x * g₁ x + f x * g₂) x := by
  have h := (hf₁.fun_mul hg.self_of_nhds).fun_add (hf.self_of_nhds.fun_mul hg₁)
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards [hf, hg] with y hyf hyg
  exact (hyf.fun_mul hyg).deriv

/-- The square rule uses `HasDerivAt.fun_pow` at exponent two. -/
theorem hasDerivAt_deriv_square {f f₁ : ℝ → ℝ} {x f₂ : ℝ}
    (hf : ∀ᶠ y in 𝓝 x, HasDerivAt f (f₁ y) y) (hf₁ : HasDerivAt f₁ f₂ x) :
    HasDerivAt (deriv (fun y => f y ^ 2)) (2 * (f₁ x) ^ 2 + 2 * f x * f₂) x := by
  have h := (hf.self_of_nhds.const_mul 2).fun_mul hf₁
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards [hf] with y hy
  simpa using (hy.fun_pow 2).deriv

/-- Nonvanishing at `x` gives local nonvanishing by continuity. -/
theorem hasDerivAt_deriv_one_div {f f₁ : ℝ → ℝ} {x f₂ : ℝ}
    (hf : ∀ᶠ y in 𝓝 x, HasDerivAt f (f₁ y) y)
    (hf₁ : HasDerivAt f₁ f₂ x) (h₀ : f x ≠ 0) :
    HasDerivAt (deriv (fun y => 1 / f y))
      (-f₂ / (f x) ^ 2 + 2 * (f₁ x) ^ 2 / (f x) ^ 3) x := by
  have hne : ∀ᶠ y in 𝓝 x, f y ≠ 0 := hf.self_of_nhds.continuousAt.eventually_ne h₀
  have hsq : HasDerivAt (fun y => f y ^ 2) (2 * f x * f₁ x) x := by
    simpa using hf.self_of_nhds.fun_pow 2
  have h := hf₁.fun_neg.fun_div hsq (pow_ne_zero 2 h₀)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · field_simp [h₀] <;> ring
  · filter_upwards [hf, hne] with y hy hyne
    simpa only [one_div] using (hy.fun_inv hyne).deriv

/-- The `(r, y₀, y₁, blend)` root box from `verify.py`. -/
def upperRoot : Fin 4 → ℚ × ℚ :=
  ![(1049 / 1000, 6 / 5), (0, 1 / 256), (-1 / 128, 1 / 128), (0, 1)]

private def thermalInput : Expr 4 := .input 0 (1049 / 1000) (6 / 5)

private def thermalSquare : Expr 4 :=
  .square ((1049 / 1000) ^ 2) ((6 / 5) ^ 2) thermalInput

private def thermalCube : Expr 4 :=
  .mul ((1049 / 1000) ^ 3) ((6 / 5) ^ 3) thermalSquare thermalInput

def thermalValue : Expr 4 := .inv (5 / 6) (1000 / 1049) thermalInput

def thermalFirst : Expr 4 :=
  .neg (-((1000 / 1049) ^ 2)) (-((5 / 6) ^ 2))
    (.inv ((5 / 6) ^ 2) ((1000 / 1049) ^ 2) thermalSquare)

def thermalSecond : Expr 4 :=
  .mul (2 * (5 / 6) ^ 3) (2 * (1000 / 1049) ^ 3) (.const 2 2 2)
    (.inv ((5 / 6) ^ 3) ((1000 / 1049) ^ 3) thermalCube)

theorem thermalChecks :
    check upperRoot thermalValue = true ∧
    check upperRoot thermalFirst = true ∧
    check upperRoot thermalSecond = true := by
  decide +kernel

noncomputable def thermalSlice (x : Fin 4 → ℝ) (r : ℝ) : ℝ :=
  value (Function.update x 0 r) thermalValue

theorem thermalSlice_apply (x : Fin 4 → ℝ) (r : ℝ) : thermalSlice x r = 1 / r := by
  simp only [thermalSlice, thermalValue, thermalInput, value, Function.update_self]

/-- Both checked derivative expressions evaluate at the point of the same
thermal slice. The second is a derivative of the ordinary `deriv`. -/
theorem thermal_hasDerivAt (x : Fin 4 → ℝ) (hr : x 0 ≠ 0) :
    HasDerivAt (thermalSlice x) (value x thermalFirst) (x 0) ∧
    HasDerivAt (deriv (thermalSlice x)) (value x thermalSecond) (x 0) := by
  have hs : thermalSlice x = fun r => 1 / r := funext (thermalSlice_apply x)
  rw [hs]
  constructor
  · change HasDerivAt (fun r : ℝ => 1 / r) (-(1 / (x 0) ^ 2)) (x 0)
    simpa only [one_div] using hasDerivAt_inv hr
  · have h := hasDerivAt_deriv_one_div (f := fun r : ℝ => r) (f₁ := fun _ => 1)
      (Filter.Eventually.of_forall fun y => hasDerivAt_id' y) (hasDerivAt_const (x 0) (1 : ℝ)) hr
    have hsecond : HasDerivAt (deriv (fun r : ℝ => 1 / r)) (2 / (x 0) ^ 3) (x 0) := by
      simpa only [neg_zero, zero_div, zero_add, one_pow, mul_one] using h
    simpa only [thermalSecond, thermalCube, thermalSquare, thermalInput, value, Rat.cast_ofNat,
      pow_succ (x 0) 2, ← mul_div_assoc, mul_one] using hsecond

/-- The existing checker encloses the slice and its two derivatives at every
real point of the closed root box. -/
theorem thermal_encloses (x : Fin 4 → ℝ)
    (hx : ∀ i, ((upperRoot i).1 : ℝ) ≤ x i ∧ x i ≤ ((upperRoot i).2 : ℝ)) :
    let f := thermalSlice x
    (5 / 6 ≤ f (x 0) ∧ f (x 0) ≤ 1000 / 1049) ∧
    (-((1000 / 1049) ^ 2) ≤ deriv f (x 0) ∧ deriv f (x 0) ≤ -((5 / 6) ^ 2)) ∧
    (2 * (5 / 6) ^ 3 ≤ deriv (deriv f) (x 0) ∧
      deriv (deriv f) (x 0) ≤ 2 * (1000 / 1049) ^ 3) := by
  have hr := (hx 0).1
  change ((1049 / 1000 : ℚ) : ℝ) ≤ x 0 at hr
  have hr₀ : 0 < x 0 := lt_of_lt_of_le (by norm_num) hr
  obtain ⟨hfirst, hsecond⟩ := thermal_hasDerivAt x hr₀.ne'
  dsimp only
  rw [hfirst.deriv, hsecond.deriv]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [thermalSlice, Function.update_eq_self, thermalValue, bounds, Rat.cast_div,
      Rat.cast_ofNat] using checked_expression_encloses upperRoot x hx thermalValue thermalChecks.1
  · simpa only [thermalFirst, bounds, Rat.cast_neg, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat]
      using checked_expression_encloses upperRoot x hx thermalFirst thermalChecks.2.1
  · simpa only [thermalSecond, bounds, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat]
      using checked_expression_encloses upperRoot x hx thermalSecond thermalChecks.2.2

end D5.S3.Quantum.Semigroups.WuCubicThermalDerivatives

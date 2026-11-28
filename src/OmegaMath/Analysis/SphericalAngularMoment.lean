import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
Omega original.

Evaluation and differentiation of closed spherical angular moments.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega

open Polynomial

/-- The closed Gamma and Pochhammer expression for the spherical angular power moment. -/
def sphericalAngularMoment (κ : ℝ) (ℓ : ℕ) (h : ℝ) : ℝ :=
  (2 : ℝ) ^ (2 * κ + 2 * h) * Real.pi ^ κ * Real.Gamma (κ + h) *
    (ascPochhammer ℝ ℓ).eval (-h) / Real.Gamma (2 * κ + h + ℓ)

private theorem gamma_mul_pochhammer {a : ℝ} (ha : 0 < a) (ℓ : ℕ) :
    Real.Gamma a * (ascPochhammer ℝ ℓ).eval a = Real.Gamma (a + ℓ) := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    have h : a + (ℓ : ℝ) ≠ 0 := by positivity
    rw [ascPochhammer_succ_eval, ← mul_assoc, ih, Nat.cast_succ, ← add_assoc,
      Real.Gamma_add_one h, mul_comm]

/-- Substitution of the first nonconformal power into the angular moment. -/
theorem sphericalAngularMoment_power {κ : ℝ} (hκ : 1 < κ) (ℓ : ℕ) :
    sphericalAngularMoment κ ℓ (1 - κ) =
      4 * Real.pi ^ κ / (Real.Gamma (κ - 1) * (((ℓ : ℝ) + κ - 1) * ((ℓ : ℝ) + κ))) := by
  let a := κ - 1 + (ℓ : ℝ)
  have hk : 0 < κ - 1 := sub_pos.mpr hκ
  have ha : 0 < a := by dsimp [a]; positivity
  have hΓ := (Real.Gamma_pos_of_pos hk).ne'
  have hΓa := (Real.Gamma_pos_of_pos ha).ne'
  have hpoch : (ascPochhammer ℝ ℓ).eval (κ - 1) = Real.Gamma a / Real.Gamma (κ - 1) :=
    (eq_div_iff hΓ).2 (by rw [mul_comm, gamma_mul_pochhammer hk])
  unfold sphericalAngularMoment
  rw [show 2 * κ + 2 * (1 - κ) = 2 by ring,
    show κ + (1 - κ) = 1 by ring, Real.Gamma_one,
    show -(1 - κ) = κ - 1 by ring, hpoch,
    show 2 * κ + (1 - κ) + (ℓ : ℝ) = a + 1 + 1 by dsimp [a]; ring,
    Real.Gamma_add_one (show a + 1 ≠ 0 by positivity), Real.Gamma_add_one ha.ne',
    show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num [Real.rpow_two]]
  have hterm : (ℓ : ℝ) + κ - 1 ≠ 0 := by
    have h := Nat.cast_nonneg (α := ℝ) ℓ
    linarith
  field_simp [hterm]
  dsimp [a]
  ring

/-- The derivative at the logarithmic power gives the angular log moment in dimension four. -/
theorem sphericalAngularMoment_log_hasDerivAt (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    HasDerivAt (sphericalAngularMoment 1 ℓ) (-4 * Real.pi / ((ℓ : ℝ) * ((ℓ : ℝ) + 1))) 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ℓ ≠ 0)
  let p := fun h : ℝ => (2 : ℝ) ^ (2 + 2 * h) * Real.pi * Real.Gamma (1 + h) *
    (ascPochhammer ℝ n).eval (-h + 1) / Real.Gamma (2 + h + (n + 1 : ℕ))
  have hfact : sphericalAngularMoment 1 (n + 1) = fun h => -h * p h := by
    funext h
    simp [sphericalAngularMoment, p, ascPochhammer_succ_left]
    ring
  have hga : DifferentiableAt ℝ Real.Gamma (1 : ℝ) :=
    (Real.hasDerivAt_Gamma_of_pos one_pos).differentiableAt
  have hgb : DifferentiableAt ℝ Real.Gamma (2 + (n + 1 : ℕ) : ℝ) :=
    (Real.hasDerivAt_Gamma_of_pos (by positivity)).differentiableAt
  have hden : Real.Gamma (2 + 0 + (n + 1 : ℕ)) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hpower : DifferentiableAt ℝ (fun x : ℝ => (2 : ℝ) ^ (2 + 2 * x)) 0 :=
    ((((hasDerivAt_id (0 : ℝ)).const_mul 2).const_add 2).const_rpow
      (show 0 < (2 : ℝ) by norm_num)).differentiableAt
  have hnum₁ : DifferentiableAt ℝ (fun x : ℝ => Real.Gamma (1 + x)) 0 := by
    have hlin : DifferentiableAt ℝ (fun x : ℝ => 1 + x) 0 := by fun_prop
    simpa [Function.comp_def] using
      ((show DifferentiableAt ℝ Real.Gamma (1 + (0 : ℝ)) by simpa using hga).comp 0 hlin)
  have hden' : DifferentiableAt ℝ (fun x : ℝ => Real.Gamma (2 + x + (n + 1 : ℕ))) 0 := by
    have hlin : DifferentiableAt ℝ (fun x : ℝ => 2 + x + (n + 1 : ℕ)) 0 := by fun_prop
    simpa [Function.comp_def] using
      ((show DifferentiableAt ℝ Real.Gamma (2 + (0 : ℝ) + (n + 1 : ℕ)) by simpa using hgb).comp 0 hlin)
  have hpoly : DifferentiableAt ℝ (fun x : ℝ => (ascPochhammer ℝ n).eval (-x + 1)) 0 := by
    have hlin : DifferentiableAt ℝ (fun x : ℝ => -x + 1) 0 := by fun_prop
    exact (Polynomial.differentiableAt (p := ascPochhammer ℝ n)).comp 0 hlin
  have hp : DifferentiableAt ℝ p 0 := by
    exact (((hpower.mul_const Real.pi).mul hnum₁).mul hpoly).div hden' hden
  have hd : HasDerivAt (fun h : ℝ => -h * p h) (-1 * p 0 + (-0 : ℝ) * deriv p 0) 0 :=
    ((hasDerivAt_id (0 : ℝ)).neg).mul hp.hasDerivAt
  rw [hfact]
  convert hd using 1
  simp only [p, neg_zero, zero_mul, mul_zero, add_zero, zero_add, neg_one_mul,
    Real.Gamma_one, mul_one, ascPochhammer_eval_one, Nat.cast_succ]
  rw [show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num [Real.rpow_two],
    show (2 + ((n : ℝ) + 1)) = ((n + 2 : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial, show n + 2 = (n + 1) + 1 by rfl,
    Nat.factorial_succ (n + 1), Nat.factorial_succ n]
  push_cast
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The leading angular coefficient in dimensions greater than four from the power moment. -/
theorem sphericalAngularCoefficient_power {κ : ℝ} (hκ : 1 < κ) (e r₁ r₂ : ℝ) (ℓ : ℕ) :
    -(Real.Gamma κ / (4 * Real.pi ^ (κ + 1)) * e / (4 * (κ - 1))) *
        r₁ * r₂ * sphericalAngularMoment κ ℓ (1 - κ) =
      -(e / (4 * Real.pi)) * r₁ * r₂ / (((ℓ : ℝ) + κ - 1) * ((ℓ : ℝ) + κ)) := by
  have hk : 0 < κ - 1 := sub_pos.mpr hκ
  have hΓ := (Real.Gamma_pos_of_pos hk).ne'
  have ha : (ℓ : ℝ) + κ - 1 ≠ 0 := by
    have h : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    linarith
  have hb : (ℓ : ℝ) + κ ≠ 0 := by positivity
  rw [sphericalAngularMoment_power hκ,
    show Real.Gamma κ = (κ - 1) * Real.Gamma (κ - 1) by
      nth_rw 1 [show κ = κ - 1 + 1 by ring]
      exact Real.Gamma_add_one hk.ne',
    Real.rpow_add Real.pi_pos, Real.rpow_one]
  field_simp [hΓ, ha, hb, hk.ne', (Real.rpow_pos_of_pos Real.pi_pos κ).ne', Real.pi_ne_zero]

/-- The leading angular coefficient in dimension four from the logarithmic moment. -/
theorem sphericalAngularCoefficient_log (e r₁ r₂ : ℝ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (Real.Gamma 1 / (4 * Real.pi ^ (2 : ℝ)) * e / 4) *
        r₁ * r₂ * deriv (sphericalAngularMoment 1 ℓ) 0 =
      -(e / (4 * Real.pi)) * r₁ * r₂ / ((ℓ : ℝ) * ((ℓ : ℝ) + 1)) := by
  have ha : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
  have hb : (ℓ : ℝ) + 1 ≠ 0 := by positivity
  rw [(sphericalAngularMoment_log_hasDerivAt ℓ hℓ).deriv, Real.Gamma_one, Real.rpow_two]
  field_simp [ha, hb, Real.pi_ne_zero]

end Omega

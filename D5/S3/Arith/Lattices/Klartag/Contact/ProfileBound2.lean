/- GID: D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/ProfileBound2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Contact.ProfileBound

open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Real
open scoped ENNReal NNReal

variable {n : ℕ}

/-- `x·e^{3x/4 − x²/8} ≤ e⁶`.  One completed square, `(x−7)² + 7 ≥ 0`, after `log x ≤ x − 1`.
The sharp constant is `e^{2.39}`; nothing downstream cares. -/
theorem mul_exp_three_quarter_le {x : ℝ} (hx : 0 < x) :
    x * Real.exp (3 * x / 4 - x ^ 2 / 8) ≤ Real.exp 6 := by
  have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx
  have hkey : Real.log x + (3 * x / 4 - x ^ 2 / 8) ≤ 6 := by nlinarith [sq_nonneg (x - 7)]
  calc x * Real.exp (3 * x / 4 - x ^ 2 / 8)
      = Real.exp (Real.log x) * Real.exp (3 * x / 4 - x ^ 2 / 8) := by rw [Real.exp_log hx]
    _ = Real.exp (Real.log x + (3 * x / 4 - x ^ 2 / 8)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp 6 := Real.exp_le_exp.2 hkey

/-- Monotonicity of `(1 − s)^{−c}` in `s`: a larger subtraction gives a larger power. -/
theorem rpow_neg_le_of_le {s₁ s₂ c : ℝ} (h : s₁ ≤ s₂) (hs₂ : s₂ < 1) (hc : 0 ≤ c) :
    (1 - s₁) ^ (-c) ≤ (1 - s₂) ^ (-c) := by
  have h2 : (0 : ℝ) < 1 - s₂ := by linarith
  have h1 : (0 : ℝ) < 1 - s₁ := by linarith
  have hle : 1 - s₂ ≤ 1 - s₁ := by linarith
  have hp : (1 - s₂) ^ c ≤ (1 - s₁) ^ c := Real.rpow_le_rpow h2.le hle hc
  rw [Real.rpow_neg h1.le, Real.rpow_neg h2.le,
    inv_le_inv₀ (Real.rpow_pos_of_pos h1 c) (Real.rpow_pos_of_pos h2 c)]
  exact hp

theorem I1_le {t : ℝ} (ht : 0 ≤ t) (hn : 0 < n) (hts : Real.sqrt t ≤ 1 / 2)
    (hint : IntegrableOn
      (fun y : ℝ => Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))) (Ioc 0 1)) :
    ((n : ℝ) * Real.sqrt t / 2) *
        ∫ y in Ioc (0 : ℝ) 1, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ Real.exp 6 * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hts2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  set x : ℝ := (n : ℝ) * Real.sqrt t with hxdef
  have hx0 : (0 : ℝ) ≤ x := by positivity

  have hpt : ∀ y ∈ Ioc (0 : ℝ) 1,
      Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
        ≤ 1 / 2 * (1 - Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)) := by
    intro y hy
    have hy1 : y ≤ 1 := hy.2
    have hys : y * Real.sqrt t ≤ Real.sqrt t := by nlinarith [hy.1.le, hs0]
    have hlt : Real.sqrt t < 1 := by linarith
    refine mul_le_mul (Phi_le_half y) (rpow_neg_le_of_le hys hlt (by positivity))
      (Real.rpow_pos_of_pos (by nlinarith [hy.1.le, hs0]) _).le (by norm_num)

  have hbound : ∫ y in Ioc (0 : ℝ) 1, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ 1 / 2 * (1 - Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)) := by
    have hle := setIntegral_mono_on hint (continuous_const.integrableOn_Ioc)
      measurableSet_Ioc hpt
    rwa [setIntegral_const, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by norm_num),
      sub_zero, smul_eq_mul, one_mul] at hle

  have hrp : (1 - Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ Real.exp (((n : ℝ) + 2) / 2 * (Real.sqrt t + Real.sqrt t ^ 2)) :=
    rpow_one_sub_le_exp hs0 hts (by positivity)
  have hexpo : ((n : ℝ) + 2) / 2 * (Real.sqrt t + Real.sqrt t ^ 2) ≤ 3 * x / 4 + 3 / 4 := by
    rw [hts2]
    have h1 : (n : ℝ) * t / 2 ≤ x / 4 := by
      rw [hxdef]
      nlinarith [hts, hs0, hts2, hn0.le]
    nlinarith [hts, hs0, hts2, hn0.le, h1]

  have habs := mul_exp_three_quarter_le (x := x)
  rcases eq_or_lt_of_le hx0 with hx | hxpos
  · have hz : x / 2 = 0 := by rw [← hx]; ring
    rw [hz, zero_mul]
    positivity
  · have hEpos : (0 : ℝ) < Real.exp (x ^ 2 / 8) := Real.exp_pos _
    have hfac : Real.exp (3 * x / 4 - x ^ 2 / 8) * Real.exp (x ^ 2 / 8)
        = Real.exp (3 * x / 4) := by
      rw [← Real.exp_add]; ring_nf
    have hstep : x * Real.exp (3 * x / 4) ≤ Real.exp 6 * Real.exp (x ^ 2 / 8) := by
      nlinarith [habs hxpos, hEpos, hfac]
    have h34 : (1 : ℝ) / 4 * Real.exp (3 / 4) ≤ 1 := by
      have h1 : Real.exp (3 / 4 : ℝ) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
      have h2 : Real.exp (1 : ℝ) < 2.7182818286 := Real.exp_one_lt_d9
      linarith
    have hkey : x / 2 * (1 / 2 * Real.exp (3 * x / 4 + 3 / 4))
        ≤ Real.exp 6 * Real.exp (x ^ 2 / 8) := by
      calc x / 2 * (1 / 2 * Real.exp (3 * x / 4 + 3 / 4))
          = (1 / 4 * Real.exp (3 / 4)) * (x * Real.exp (3 * x / 4)) := by
            rw [Real.exp_add]; ring
        _ ≤ 1 * (Real.exp 6 * Real.exp (x ^ 2 / 8)) :=
            mul_le_mul h34 hstep (by positivity) (by norm_num)
        _ = Real.exp 6 * Real.exp (x ^ 2 / 8) := by ring
    have hxsq : x ^ 2 / 8 = (n : ℝ) ^ 2 * t / 8 := by
      rw [hxdef, mul_pow, hts2]
    calc ((n : ℝ) * Real.sqrt t / 2) *
          ∫ y in Ioc (0 : ℝ) 1, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
        ≤ (x / 2) * (1 / 2 * (1 - Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))) := by
          refine mul_le_mul_of_nonneg_left hbound (by positivity)
      _ ≤ (x / 2) * (1 / 2 * Real.exp (3 * x / 4 + 3 / 4)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num))
            (by positivity)
          exact le_trans hrp (Real.exp_le_exp.2 hexpo)
      _ ≤ Real.exp 6 * Real.exp (x ^ 2 / 8) := hkey
      _ = Real.exp 6 * Real.exp ((n : ℝ) ^ 2 * t / 8) := by rw [hxsq]

section I3

/-- Integrability of the shifted Gaussian over `y` on `Ioc A B`, `A > 0`. -/
theorem integrableOn_gauss_div_Ioc {A B b : ℝ} (hA : 0 < A) :
    IntegrableOn (fun y : ℝ => Real.exp (-(y - b) ^ 2 / 2) / y) (Ioc A B) := by
  have hcont : ContinuousOn (fun y : ℝ => Real.exp (-(y - b) ^ 2 / 2) / y) (Icc A B) := by
    refine ContinuousOn.div (by fun_prop) continuousOn_id (fun y hy => ?_)
    have : A ≤ y := hy.1
    linarith
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set (fun y hy => ⟨hy.1.le, hy.2⟩)

/-- **The crude Gaussian bound.**  `∫_A^B e^{−(y−b)²/2}/y dy ≤ √(2π)/A`: no split, just
`1/y ≤ 1/A` and the total mass. -/
theorem gaussian_over_y_crude {A B b : ℝ} (hA : 0 < A) :
    ∫ y in Ioc A B, Real.exp (-(y - b) ^ 2 / 2) / y ≤ Real.sqrt (2 * π) / A := by
  have hmono : ∫ y in Ioc A B, Real.exp (-(y - b) ^ 2 / 2) / y
      ≤ ∫ y in Ioc A B, 1 / A * Real.exp (-(y - b) ^ 2 / 2) := by
    refine setIntegral_mono_on (integrableOn_gauss_div_Ioc hA)
      (((integrable_shifted_gaussian b).const_mul _).integrableOn) measurableSet_Ioc
      (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := lt_trans hA hy.1
    have hinv : 1 / y ≤ 1 / A := by
      rw [div_le_div_iff₀ hy0 hA]
      linarith [hy.1.le]
    calc Real.exp (-(y - b) ^ 2 / 2) / y = Real.exp (-(y - b) ^ 2 / 2) * (1 / y) := by ring
      _ ≤ Real.exp (-(y - b) ^ 2 / 2) * (1 / A) :=
          mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le
      _ = 1 / A * Real.exp (-(y - b) ^ 2 / 2) := by ring
  refine le_trans hmono ?_
  rw [MeasureTheory.integral_const_mul]
  have hmass : ∫ y in Ioc A B, Real.exp (-(y - b) ^ 2 / 2) ≤ Real.sqrt (2 * π) := by
    rw [← integral_shifted_gaussian b]
    exact setIntegral_le_integral (integrable_shifted_gaussian b)
      (Filter.Eventually.of_forall (fun y => (Real.exp_pos _).le))
  calc 1 / A * ∫ y in Ioc A B, Real.exp (-(y - b) ^ 2 / 2)
      ≤ 1 / A * Real.sqrt (2 * π) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = Real.sqrt (2 * π) / A := by ring

/-- **The generic piece bound.**  `Lemma43.oneDim_le` on an arbitrary `Ioc A B` with `A ≥ 1`; the
frozen version is hard-coded to `A = 1`. -/
theorem piece_le {t J K A B : ℝ} (ht : 0 ≤ t) (hA : 1 ≤ A)
    (hBs : B * Real.sqrt t ≤ 1 / 2)
    (hJ : ∀ y ∈ Ioc A B,
      y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ J)
    (hint1 : IntegrableOn
      (fun y : ℝ => Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))) (Ioc A B))
    (hint2 : IntegrableOn (fun y : ℝ =>
      Real.exp J / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8)
        * (Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2) / y)) (Ioc A B))
    (hK : ∫ y in Ioc A B,
      Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2) / y ≤ K) :
    ∫ y in Ioc A B, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ Real.exp J * K / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
  have hs0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hsq : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  have hmono : ∫ y in Ioc A B, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ ∫ y in Ioc A B, Real.exp J / Real.sqrt (2 * π)
          * Real.exp ((n : ℝ) ^ 2 * t / 8)
          * (Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2) / y) := by
    refine setIntegral_mono_on hint1 hint2 measurableSet_Ioc (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hA) hy.1.le
    have hys : y * Real.sqrt t ≤ 1 / 2 :=
      le_trans (mul_le_mul_of_nonneg_right hy.2 hs0) hBs
    have h := integrand_le (n := n) ht hy0 hys (hJ y hy)
    refine le_trans h (le_of_eq ?_)
    field_simp
  refine le_trans hmono ?_
  rw [MeasureTheory.integral_const_mul]
  have hconst : (0 : ℝ) ≤ Real.exp J / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
    positivity
  calc Real.exp J / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8)
        * ∫ y in Ioc A B, Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2) / y
      ≤ Real.exp J / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8) * K :=
        mul_le_mul_of_nonneg_left hK hconst
    _ = Real.exp J * K / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8) := by ring

/-- **`I₃` with its prefactor.**  `b ≤ 2A` makes the constant `2·e^J`, with no `n` and no `t`
outside the exponential. -/
theorem I3_le {t J A B : ℝ} (ht : 0 ≤ t) (hA : 1 ≤ A) (hBs : B * Real.sqrt t ≤ 1 / 2)
    (hbA : (n : ℝ) * Real.sqrt t / 2 ≤ 2 * A)
    (hJ : ∀ y ∈ Ioc A B,
      y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ J)
    (hint1 : IntegrableOn
      (fun y : ℝ => Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))) (Ioc A B))
    (hint2 : IntegrableOn (fun y : ℝ =>
      Real.exp J / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8)
        * (Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2) / y)) (Ioc A B)) :
    ((n : ℝ) * Real.sqrt t / 2) *
        ∫ y in Ioc A B, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ 2 * Real.exp J * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hb0 : (0 : ℝ) ≤ (n : ℝ) * Real.sqrt t / 2 := by positivity
  have hsq : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  have hone := piece_le (n := n) ht hA hBs hJ hint1 hint2
    (gaussian_over_y_crude (b := (n : ℝ) * Real.sqrt t / 2) hA0)
  calc ((n : ℝ) * Real.sqrt t / 2) *
        ∫ y in Ioc A B, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ ((n : ℝ) * Real.sqrt t / 2) *
          (Real.exp J * (Real.sqrt (2 * π) / A) / Real.sqrt (2 * π)
            * Real.exp ((n : ℝ) ^ 2 * t / 8)) := mul_le_mul_of_nonneg_left hone hb0
    _ = ((n : ℝ) * Real.sqrt t / 2) * (Real.exp J / A) * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
        field_simp
    _ ≤ (2 * A) * (Real.exp J / A) * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbA (by positivity)) ?_
        exact (Real.exp_pos _).le
    _ = 2 * Real.exp J * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
        field_simp

end I3

end D5.S3.Arith.Lattices.Klartag

/- GID: D5/S3/Analytic/Polynomial/HermiteMaxCoefficientRatios
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/HermiteMaxCoefficientRatios
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Sqrt]
   utility: none
   digest: Closed forms, exact ratios and limits of the maximal signed and absolute Hermite coefficients. -/

import D5.S3.Analytic.Polynomial.HermiteAbsoluteModeBlocks
import D5.S3.Analytic.Polynomial.HermiteSignedModeBlocks
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The signed and absolute maximal coefficients `B(n)` and `M(n)` of the physicists' Hermite
polynomial: closed forms, `B ≤ M`, the exact value of `B/M` in each interlacing case, the exact
successive ratios in each transition case, and the limits `B/M → 1`,
`B(n+1)/(B(n)√n) → √2` and `M(n+1)/(M(n)√n) → √2`.

admission_basis: escape-witness. Escape witnesses: B_ratio and M_ratio (exact successive ratios
from the closed forms), BM_ratio (exact `B/M` in the three interlacing cases), near_sqrt_lim with
a_lim and b_lim (`a/√n → √2`, `b/√n → √2` from the explicit `O(1)` bounds), q_lim and t_lim, and the
case limits g1_lim, g2_lim, h2_lim, r1_lim, r2_lim. Consumed bind-only helpers: coeff_formula,
B_formula, M_formula, B_pos, M_pos, q_step, t_step, B_le_M, inv_sqrt_lim, inv_nat_lim, n1_lim,
either_lim, either3_lim, s2_ne, s2_sq. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Polynomial.HermiteMaxCoefficientRatios

open Filter Topology
open D5.S3.Analytic.Polynomial
open D5.S3.Analytic.Polynomial.HermiteAbsoluteModeBlocks

local notation "q" => HermiteSignedMode.mode
local notation "t" => HermiteAbsoluteMode.mode
local notation "aa" => HermiteSignedMode.a
local notation "bb" => HermiteAbsoluteMode.b

private theorem coeff_formula (n r : ℕ) (hr : 2 * r ≤ n) :
    (HermiteSignedMode.physicistsHermite n).coeff (n - 2 * r) =
      (-1) ^ r * ((n.factorial : ℚ) * 2 ^ (n - 2 * r) / (r.factorial * (n - 2 * r).factorial)) := by
  rw [HermiteSignedMode.polynomial_coeff n _ (Nat.sub_le _ _)]
  have h : n - 2 * r ≤ n ∧ (n - (n - 2 * r)) % 2 = 0 := by constructor <;> omega
  rw [HermiteSignedMode.signedCoeff, if_pos h, show n - (n - 2 * r) = 2 * r by omega,
    show 2 * r / 2 = r by omega]
  ring

private theorem B_formula (n : ℕ) :
    signedMax n = (n.factorial : ℚ) * 2 ^ aa n / ((2 * q n).factorial * (aa n).factorial) := by
  have hq := (HermiteSignedMode.mode_rises n).1
  have := coeff_formula n (2 * q n) (by omega)
  rw [show n - 2 * (2 * q n) = aa n by unfold HermiteSignedMode.a; omega, pow_mul] at this
  simp only [neg_one_sq, one_pow, one_mul] at this
  exact this

private theorem M_formula (n : ℕ) :
    absMax n = (n.factorial : ℚ) * 2 ^ bb n / ((t n).factorial * (bb n).factorial) := by
  have ht := (HermiteAbsoluteMode.mode_rises n).1
  have := coeff_formula n (t n) ht
  rw [show n - 2 * t n = bb n from rfl] at this
  rw [absMax, this, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (by positivity)]

private theorem B_pos (n : ℕ) : 0 < signedMax n := by rw [B_formula]; positivity
private theorem M_pos (n : ℕ) : 0 < absMax n := by rw [M_formula]; positivity

private theorem q_step (n : ℕ) : q n ≤ q (n + 1) ∧ q (n + 1) ≤ q n + 1 := by
  have h := HermiteSignedMode.result.2 n
  have h1 := (HermiteSignedMode.mode_rises n).1
  have h2 := (HermiteSignedMode.mode_rises (n + 1)).1
  simp only [HermiteSignedMode.a] at h
  push_cast [h1, h2] at h
  omega

private theorem B_ratio (n : ℕ) :
    (q (n + 1) = q n ∧ signedMax (n + 1) / signedMax n = 2 * (n + 1) / (aa n + 1)) ∨
    (q (n + 1) = q n + 1 ∧ 3 ≤ aa n ∧ signedMax (n + 1) / signedMax n =
      (n + 1) * aa n * (aa n - 1) * (aa n - 2) / (8 * (2 * q n + 1) * (2 * q n + 2))) := by
  have hs := q_step n
  have h1 := (HermiteSignedMode.mode_rises n).1
  have h2 := (HermiteSignedMode.mode_rises (n + 1)).1
  rw [B_formula, B_formula]
  rcases (show q (n + 1) = q n ∨ q (n + 1) = q n + 1 by omega) with h | h
  · left
    refine ⟨h, ?_⟩
    have ha : aa (n + 1) = aa n + 1 := by unfold HermiteSignedMode.a; rw [h]; omega
    rw [ha, h, Nat.factorial_succ n, Nat.factorial_succ (aa n)]
    push_cast
    field_simp
    ring
  · right
    have ha3 : 3 ≤ aa n := by unfold HermiteSignedMode.a; omega
    have ha : aa (n + 1) + 3 = aa n := by unfold HermiteSignedMode.a; rw [h]; omega
    refine ⟨h, ha3, ?_⟩
    obtain ⟨c, hc⟩ : ∃ c, aa (n + 1) = c := ⟨_, rfl⟩
    rw [hc] at ha ⊢
    rw [← ha, h, show 2 * (q n + 1) = 2 * q n + 1 + 1 by ring, Nat.factorial_succ (2 * q n + 1),
      Nat.factorial_succ (2 * q n), Nat.factorial_succ n, show c + 3 = c + 2 + 1 by ring,
      Nat.factorial_succ (c + 2), Nat.factorial_succ (c + 1), Nat.factorial_succ c]
    push_cast
    field_simp
    ring

private theorem M_ratio (n : ℕ) :
    (t (n + 1) = t n ∧ absMax (n + 1) / absMax n = 2 * (n + 1) / (bb n + 1)) ∨
    (t (n + 1) = t n + 1 ∧ 1 ≤ bb n ∧
      absMax (n + 1) / absMax n = (n + 1) * bb n / (2 * (t n + 1))) := by
  have hs := HermiteAbsoluteMode.mode_step n
  have h1 := (HermiteAbsoluteMode.mode_rises n).1
  have h2 := (HermiteAbsoluteMode.mode_rises (n + 1)).1
  rw [M_formula, M_formula]
  rcases (show t (n + 1) = t n ∨ t (n + 1) = t n + 1 by omega) with h | h
  · left
    refine ⟨h, ?_⟩
    have hb : bb (n + 1) = bb n + 1 := by unfold HermiteAbsoluteMode.b; rw [h]; omega
    rw [hb, h, Nat.factorial_succ n, Nat.factorial_succ (bb n)]
    push_cast
    field_simp
    ring
  · right
    have hb1 : 1 ≤ bb n := by unfold HermiteAbsoluteMode.b; omega
    have hb : bb (n + 1) + 1 = bb n := by unfold HermiteAbsoluteMode.b; rw [h]; omega
    refine ⟨h, hb1, ?_⟩
    obtain ⟨c, hc⟩ : ∃ c, bb (n + 1) = c := ⟨_, rfl⟩
    rw [hc] at hb ⊢
    rw [← hb, h, Nat.factorial_succ (t n), Nat.factorial_succ n, Nat.factorial_succ c]
    push_cast
    field_simp
    ring


private theorem inv_sqrt_lim : Tendsto (fun n : ℕ => 1 / √(n : ℝ)) atTop (𝓝 0) := by
  have h := ((Real.continuous_sqrt.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat)
  rw [Real.sqrt_zero] at h
  refine h.congr fun n => ?_
  simp [Function.comp, Real.sqrt_inv]

private theorem inv_nat_lim : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
  tendsto_one_div_atTop_nhds_zero_nat

private theorem near_sqrt_lim (x : ℕ → ℝ) (C : ℝ) (hx : ∀ n, |x n - √(2 * n)| ≤ C) :
    Tendsto (fun n : ℕ => x n / √(n : ℝ)) atTop (𝓝 √2) := by
  have h0 : Tendsto (fun n : ℕ => x n / √(n : ℝ) - √2) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using inv_sqrt_lim.const_mul C)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have e : x n / √(n : ℝ) - √2 = (x n - √(2 * n)) * (1 / √(n : ℝ)) := by
      rw [Real.sqrt_mul (by norm_num)]; field_simp
    rw [e, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / √(n:ℝ))]
    simp only [one_div]
    exact mul_le_mul_of_nonneg_right (hx n) (inv_nonneg.2 hs.le)
  simpa using h0.add_const √2

private theorem either_lim (f g h : ℕ → ℝ) (L : ℝ) (hg : Tendsto g atTop (𝓝 L))
    (hh : Tendsto h atTop (𝓝 L)) (hf : ∀ᶠ n in atTop, f n = g n ∨ f n = h n) :
    Tendsto f atTop (𝓝 L) := by
  have hg' := tendsto_iff_norm_sub_tendsto_zero.1 hg
  have hh' := tendsto_iff_norm_sub_tendsto_zero.1 hh
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero_norm' ?_ (by simpa using hg'.add hh'))
  filter_upwards [hf] with n hn
  rw [norm_norm]
  rcases hn with e | e <;> rw [e]
  · exact le_add_of_nonneg_right (abs_nonneg _)
  · exact le_add_of_nonneg_left (abs_nonneg _)

private theorem either3_lim (f g h k : ℕ → ℝ) (L : ℝ) (hg : Tendsto g atTop (𝓝 L))
    (hh : Tendsto h atTop (𝓝 L)) (hk : Tendsto k atTop (𝓝 L))
    (hf : ∀ᶠ n in atTop, f n = g n ∨ f n = h n ∨ f n = k n) :
    Tendsto f atTop (𝓝 L) := by
  have hg' := tendsto_iff_norm_sub_tendsto_zero.1 hg
  have hh' := tendsto_iff_norm_sub_tendsto_zero.1 hh
  have hk' := tendsto_iff_norm_sub_tendsto_zero.1 hk
  refine tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero_norm' ?_ (by simpa using (hg'.add hh').add hk'))
  filter_upwards [hf] with n hn
  rw [norm_norm]
  have := abs_nonneg (g n - L); have := abs_nonneg (h n - L); have := abs_nonneg (k n - L)
  simp only [Real.norm_eq_abs]
  rcases hn with e | e | e <;> rw [e] <;> linarith

private theorem a_lim : Tendsto (fun n : ℕ => (aa n : ℝ) / √(n : ℝ)) atTop (𝓝 √2) := by
  refine near_sqrt_lim _ (7 / 2) fun n => ?_
  have h := (HermiteSignedModeBlocks.result.2.2.2.2.2.2.2.2.2.2.1) n
  rw [abs_le]; constructor <;> linarith [h.1, h.2]

private theorem b_lim : Tendsto (fun n : ℕ => (bb n : ℝ) / √(n : ℝ)) atTop (𝓝 √2) := by
  refine near_sqrt_lim _ (5 / 2) fun n => ?_
  have h := (result.2.2.2.2.1) n
  rw [abs_le]; constructor <;> linarith [h.2.1, h.2.2]

private theorem q_lim : Tendsto (fun n : ℕ => (q n : ℝ) / n) atTop (𝓝 (1 / 4)) := by
  have h := (a_lim.mul inv_sqrt_lim).const_mul (1 / 4 : ℝ)
  have h2 := h.const_sub (1 / 4 : ℝ)
  simp only [mul_zero, sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hq := (HermiteSignedMode.mode_rises n).1
  have e : (aa n : ℝ) = n - 4 * q n := by
    unfold HermiteSignedMode.a; push_cast [hq]; ring
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hp : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  rw [e]
  generalize √(n : ℝ) = s at hs hp ⊢
  rw [← hs]; field_simp; ring

private theorem t_lim : Tendsto (fun n : ℕ => (t n : ℝ) / n) atTop (𝓝 (1 / 2)) := by
  have h := (b_lim.mul inv_sqrt_lim).const_mul (1 / 2 : ℝ)
  have h2 := h.const_sub (1 / 2 : ℝ)
  simp only [mul_zero, sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have ht := (HermiteAbsoluteMode.mode_rises n).1
  have e : (bb n : ℝ) = n - 2 * t n := by
    unfold HermiteAbsoluteMode.b; push_cast [ht]; ring
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hp : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  rw [e]
  generalize √(n : ℝ) = s at hs hp ⊢
  rw [← hs]; field_simp; ring

private theorem n1_lim : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
  have h := inv_nat_lim.const_add 1
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

private theorem s2_sq : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)

private theorem g1_lim (x : ℕ → ℕ) (hx : Tendsto (fun n : ℕ => (x n : ℝ) / √(n : ℝ)) atTop (𝓝 √2)) :
    Tendsto (fun n : ℕ => 2 * (((n : ℝ) + 1) / n) / ((x n : ℝ) / √(n : ℝ) + 1 / √(n : ℝ)))
      atTop (𝓝 √2) := by
  have h := (n1_lim.const_mul 2).div (hx.add inv_sqrt_lim) (by simp)
  convert h using 2
  field_simp; linarith [s2_sq]

private theorem g2_lim : Tendsto (fun n : ℕ =>
    ((n : ℝ) + 1) / n * ((aa n : ℝ) / √(n : ℝ)) * ((aa n : ℝ) / √(n : ℝ) - 1 / √(n : ℝ)) *
      ((aa n : ℝ) / √(n : ℝ) - 2 * (1 / √(n : ℝ))) /
      (8 * (2 * ((q n : ℝ) / n) + 1 / n) * (2 * ((q n : ℝ) / n) + 2 * (1 / n)))) atTop (𝓝 √2) := by
  have h := (((n1_lim.mul a_lim).mul (a_lim.sub inv_sqrt_lim)).mul
    (a_lim.sub (inv_sqrt_lim.const_mul 2))).div
    (((q_lim.const_mul 2).add inv_nat_lim).const_mul 8 |>.mul
      ((q_lim.const_mul 2).add (inv_nat_lim.const_mul 2))) (by norm_num)
  convert h using 2
  norm_num

private theorem h2_lim : Tendsto (fun n : ℕ =>
    ((n : ℝ) + 1) / n * ((bb n : ℝ) / √(n : ℝ)) / (2 * ((t n : ℝ) / n + 1 / n))) atTop (𝓝 √2) := by
  have h := (n1_lim.mul b_lim).div ((t_lim.add inv_nat_lim).const_mul 2) (by norm_num)
  convert h using 2
  norm_num

private theorem r1_lim : Tendsto (fun n : ℕ =>
    (bb n : ℝ) / √(n : ℝ) * ((bb n : ℝ) / √(n : ℝ) - 1 / √(n : ℝ)) /
      (4 * ((t n : ℝ) / n + 1 / n))) atTop (𝓝 1) := by
  have h := (b_lim.mul (b_lim.sub inv_sqrt_lim)).div ((t_lim.add inv_nat_lim).const_mul 4)
    (by norm_num)
  convert h using 2
  norm_num

private theorem r2_lim : Tendsto (fun n : ℕ =>
    4 * ((t n : ℝ) / n) / (((bb n : ℝ) / √(n : ℝ) + 1 / √(n : ℝ)) *
      ((bb n : ℝ) / √(n : ℝ) + 2 * (1 / √(n : ℝ))))) atTop (𝓝 1) := by
  have h := (t_lim.const_mul 4).div ((b_lim.add inv_sqrt_lim).mul
    (b_lim.add (inv_sqrt_lim.const_mul 2))) (by norm_num)
  convert h using 2
  norm_num

private theorem signed_ratio_lim :
    Tendsto (fun n : ℕ => (signedMax (n + 1) : ℝ) / ((signedMax n : ℝ) * √(n : ℝ))) atTop
      (𝓝 √2) := by
  refine either_lim _ _ _ _ (g1_lim _ a_lim) g2_lim ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  rw [← div_div, ← Rat.cast_div]
  rcases B_ratio n with ⟨-, h⟩ | ⟨hq, -, h⟩
  · left
    rw [h]; push_cast
    generalize √(n : ℝ) = s at hs hp ⊢
    rw [← hs]; field_simp
  · right
    rw [h]; push_cast
    generalize √(n : ℝ) = s at hs hp ⊢
    rw [← hs]; field_simp

private theorem abs_ratio_lim :
    Tendsto (fun n : ℕ => (absMax (n + 1) : ℝ) / ((absMax n : ℝ) * √(n : ℝ))) atTop
      (𝓝 √2) := by
  refine either_lim _ _ _ _ (g1_lim _ b_lim) h2_lim ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  rw [← div_div, ← Rat.cast_div]
  rcases M_ratio n with ⟨-, h⟩ | ⟨-, -, h⟩
  · left
    rw [h]; push_cast
    generalize √(n : ℝ) = s at hs hp ⊢
    rw [← hs]; field_simp
  · right
    rw [h]; push_cast
    generalize √(n : ℝ) = s at hs hp ⊢
    rw [← hs]; field_simp

private theorem BM_ratio (n : ℕ) :
    (aa n = bb n ∧ signedMax n / absMax n = 1) ∨
    (aa n = bb n + 2 ∧ signedMax n / absMax n = 4 * t n / ((bb n + 1) * (bb n + 2))) ∨
    (aa n + 2 = bb n ∧ signedMax n / absMax n = bb n * (bb n - 1) / (4 * (t n + 1))) := by
  have hq := (HermiteSignedMode.mode_rises n).1
  have ht := (HermiteAbsoluteMode.mode_rises n).1
  have hM := M_pos n
  rw [B_formula, M_formula]
  rcases result.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 n with h | h | h
  · right; right
    have e1 : 2 * q n = t n + 1 := by
      unfold HermiteSignedMode.a HermiteAbsoluteMode.b at h; push_cast [hq, ht] at h; omega
    have e2 : aa n + 2 = bb n := by
      unfold HermiteSignedMode.a HermiteAbsoluteMode.b; omega
    refine ⟨e2, ?_⟩
    rw [e1, ← e2, Nat.factorial_succ (t n), show aa n + 2 = aa n + 1 + 1 by ring,
      Nat.factorial_succ (aa n + 1), Nat.factorial_succ (aa n)]
    push_cast
    field_simp
    ring
  · left
    have e1 : 2 * q n = t n := by
      unfold HermiteSignedMode.a HermiteAbsoluteMode.b at h; push_cast [hq, ht] at h; omega
    have e2 : aa n = bb n := by
      unfold HermiteSignedMode.a HermiteAbsoluteMode.b; omega
    refine ⟨e2, ?_⟩
    rw [e1, e2]
    exact div_self (by positivity)
  · right; left
    have e1 : 2 * q n + 1 = t n := by
      unfold HermiteSignedMode.a HermiteAbsoluteMode.b at h; push_cast [hq, ht] at h; omega
    have e2 : aa n = bb n + 2 := by
      unfold HermiteSignedMode.a HermiteAbsoluteMode.b; omega
    refine ⟨e2, ?_⟩
    rw [← e1, e2, Nat.factorial_succ (2 * q n), show bb n + 2 = bb n + 1 + 1 by ring,
      Nat.factorial_succ (bb n + 1), Nat.factorial_succ (bb n)]
    push_cast
    field_simp
    ring

private theorem B_le_M (n : ℕ) : signedMax n ≤ absMax n := by
  have hq := (HermiteSignedMode.mode_rises n).1
  have h1 : signedMax n ≤ HermiteAbsoluteMode.weight n (2 * q n) := by
    rw [HermiteAbsoluteMode.weight, show n - 2 * (2 * q n) = aa n by
      unfold HermiteSignedMode.a; omega, signedMax,
      HermiteSignedMode.polynomial_coeff n (aa n) (Nat.sub_le _ _)]
    exact le_abs_self _
  have h2 : absMax n = HermiteAbsoluteMode.weight n (t n) := by
    rw [absMax, HermiteSignedMode.polynomial_coeff n (bb n) (Nat.sub_le _ _)]; rfl
  rw [h2]
  exact h1.trans (HermiteAbsoluteMode.weight_le_mode n _ (by omega))

private theorem BM_lim : Tendsto (fun n : ℕ => (signedMax n : ℝ) / absMax n) atTop (𝓝 1) := by
  have h3 : ∀ᶠ n in atTop, (signedMax n : ℝ) / absMax n = 1 ∨
      (signedMax n : ℝ) / absMax n =
        4 * ((t n : ℝ) / n) / (((bb n : ℝ) / √(n : ℝ) + 1 / √(n : ℝ)) *
          ((bb n : ℝ) / √(n : ℝ) + 2 * (1 / √(n : ℝ)))) ∨
      (signedMax n : ℝ) / absMax n =
        (bb n : ℝ) / √(n : ℝ) * ((bb n : ℝ) / √(n : ℝ) - 1 / √(n : ℝ)) /
          (4 * ((t n : ℝ) / n + 1 / n)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hp : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    rw [← Rat.cast_div]
    rcases BM_ratio n with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> push_cast
    · left; rfl
    · right; left
      generalize √(n : ℝ) = s at hs hp ⊢
      rw [← hs]; field_simp
    · right; right
      generalize √(n : ℝ) = s at hs hp ⊢
      rw [← hs]; field_simp
  refine either3_lim _ (fun _ => 1) _ _ 1 tendsto_const_nhds r2_lim r1_lim ?_
  simpa using h3

/-- Corollary 5 of Ma and Zhang, with equations (6) and (14), for the signed and absolute maximal
coefficients `B(n)` (A277280) and `M(n)` (A277281) of the physicists' Hermite polynomial, where
`a(n) = n - 4q(n)` and `b(n) = n - 2t(n)` are the least signed and absolute maximizing exponents:
the closed forms of `B` and `M`; `0 < B ≤ M`, so the denominators `B(n)√n` and `M(n)√n` are positive
for `n ≥ 1`; the exact value of `B/M` in each interlacing case `a ∈ {b, b + 2, b - 2}`; the exact
successive ratios of `B` and `M` in each transition case; and the limits `B(n)/M(n) → 1`,
`B(n + 1)/(B(n)√n) → √2` and `M(n + 1)/(M(n)√n) → √2`. -/
theorem result :
    (∀ n : ℕ, signedMax n = (n.factorial : ℚ) * 2 ^ aa n / ((2 * q n).factorial * (aa n).factorial) ∧
      absMax n = (n.factorial : ℚ) * 2 ^ bb n / ((t n).factorial * (bb n).factorial)) ∧
    (∀ n : ℕ, 0 < signedMax n ∧ signedMax n ≤ absMax n) ∧
    (∀ n : ℕ, 1 ≤ n → 0 < (signedMax n : ℝ) * √(n : ℝ) ∧ 0 < (absMax n : ℝ) * √(n : ℝ)) ∧
    (∀ n : ℕ, (aa n = bb n ∧ signedMax n / absMax n = 1) ∨
      (aa n = bb n + 2 ∧ signedMax n / absMax n = 4 * t n / ((bb n + 1) * (bb n + 2))) ∨
      (aa n + 2 = bb n ∧ signedMax n / absMax n = bb n * (bb n - 1) / (4 * (t n + 1)))) ∧
    (∀ n : ℕ, (q (n + 1) = q n ∧ signedMax (n + 1) / signedMax n = 2 * (n + 1) / (aa n + 1)) ∨
      (q (n + 1) = q n + 1 ∧ 3 ≤ aa n ∧ signedMax (n + 1) / signedMax n =
        (n + 1) * aa n * (aa n - 1) * (aa n - 2) / (8 * (2 * q n + 1) * (2 * q n + 2)))) ∧
    (∀ n : ℕ, (t (n + 1) = t n ∧ absMax (n + 1) / absMax n = 2 * (n + 1) / (bb n + 1)) ∨
      (t (n + 1) = t n + 1 ∧ 1 ≤ bb n ∧
        absMax (n + 1) / absMax n = (n + 1) * bb n / (2 * (t n + 1)))) ∧
    Tendsto (fun n : ℕ => (signedMax n : ℝ) / absMax n) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => (signedMax (n + 1) : ℝ) / ((signedMax n : ℝ) * √(n : ℝ))) atTop
      (𝓝 √2) ∧
    Tendsto (fun n : ℕ => (absMax (n + 1) : ℝ) / ((absMax n : ℝ) * √(n : ℝ))) atTop (𝓝 √2) :=
  ⟨fun n => ⟨B_formula n, M_formula n⟩, fun n => ⟨B_pos n, B_le_M n⟩,
    fun n hn => have hp : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
      ⟨mul_pos (by exact_mod_cast B_pos n) hp, mul_pos (by exact_mod_cast M_pos n) hp⟩,
    BM_ratio, B_ratio, M_ratio, BM_lim, signed_ratio_lim, abs_ratio_lim⟩

end D5.S3.Analytic.Polynomial.HermiteMaxCoefficientRatios

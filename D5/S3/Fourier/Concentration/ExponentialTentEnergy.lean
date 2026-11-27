/- GID: D5/S3/Fourier/Concentration/ExponentialTentEnergy
   generality: I
   mirror-B: D5/B/S3/Fourier/Concentration/ExponentialTentEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An exponential weight gives an attained minimum and a cubic lower bound for a nonnegative peak. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Weighted energy of a nonnegative profile with a prescribed central value and a one-sided slope bound. -/

namespace D5.S3.Fourier.Concentration.ExponentialTentEnergy

open MeasureTheory Set
open scoped Interval

/-- The nonnegative profile of a peak of height `a` with slope bounded by `L`. -/
noncomputable def tent (a L x : ℝ) : ℝ := max (a - L * |x|) 0

private theorem tent_at_zero {a : ℝ} (ha : 0 ≤ a) (L : ℝ) : tent a L 0 = a := by
  simp [tent, max_eq_left ha]

private theorem tent_eq_linear {a L x : ℝ} (hL : 0 < L) (hx : |x| ≤ a / L) :
    tent a L x = a - L * |x| := by
  rw [tent, max_eq_left]
  have h := (le_div_iff₀ hL).mp hx
  linarith

private theorem tent_eq_zero {a L x : ℝ} (hL : 0 < L) (hx : a / L ≤ |x|) :
    tent a L x = 0 := by
  rw [tent, max_eq_right]
  have h := (div_le_iff₀ hL).mp hx
  linarith

private theorem tent_energy_integrable (a : ℝ) {L : ℝ} (hL : 0 < L) :
    Integrable (fun x : ℝ => Real.exp (-2 * |x|) * tent a L x ^ 2) := by
  have hc : Continuous (fun x : ℝ => Real.exp (-2 * |x|) * tent a L x ^ 2) := by
    unfold tent
    fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(a / L)) (b := a / L))
  intro x hx
  by_contra hout
  have hrad : a / L ≤ |x| := le_of_lt (lt_of_not_ge fun h => hout (abs_le.mp h))
  exact hx (by simp [tent_eq_zero hL hrad])

private theorem tent_energy_le (f : ℝ → ℝ) (L : ℝ) (hn : ∀ x, 0 ≤ f x)
    (hpeak : ∀ x, f 0 - L * |x| ≤ f x)
    (hi : Integrable (fun x : ℝ => Real.exp (-2 * |x|) * f x ^ 2)) (hL : 0 < L) :
    (∫ x : ℝ, Real.exp (-2 * |x|) * tent (f 0) L x ^ 2) ≤
      ∫ x : ℝ, Real.exp (-2 * |x|) * f x ^ 2 := by
  apply integral_mono (tent_energy_integrable _ hL) hi
  intro x
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  exact pow_le_pow_left₀ (le_max_right _ _) (max_le (hpeak x) (hn x)) 2

private theorem tent_energy_eq_half {a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L) :
    (∫ x : ℝ, Real.exp (-2 * |x|) * tent a L x ^ 2) =
      2 * ∫ x in 0..a / L, Real.exp (-2 * x) * (a - L * x) ^ 2 := by
  let r := a / L
  let e (x : ℝ) := Real.exp (-2 * |x|) * tent a L x ^ 2
  have hr : 0 ≤ r := div_nonneg ha hL.le
  have horder : -r ≤ r := by linarith
  have hc : Continuous e := by
    dsimp [e, tent]
    fun_prop
  have hrestrict : (∫ x : ℝ, e x) = ∫ x in -r..r, e x := by
    rw [intervalIntegral.integral_of_le horder, ← integral_Icc_eq_integral_Ioc,
      ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ Icc (-r) r
    · exact (indicator_of_mem hx _).symm
    · have hx' : r ≤ |x| := le_of_lt (lt_of_not_ge fun habs => hx (abs_le.mp habs))
      simp [indicator_of_notMem hx, e, tent_eq_zero hL hx']
  have hreflect : (∫ x in -r..0, e x) = ∫ x in 0..r, e x := by
    rw [← neg_zero, ← intervalIntegral.integral_comp_neg]
    simp only [neg_zero, e, tent, abs_neg]
  change (∫ x : ℝ, e x) = 2 * ∫ x in 0..r, Real.exp (-2 * x) * (a - L * x) ^ 2
  rw [hrestrict, ← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-r) 0) (hc.intervalIntegrable 0 r), hreflect, ← two_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hr] at hx
  have habs : |x| ≤ a / L := by simpa [abs_of_nonneg hx.1, r] using hx.2
  simp only [e, tent_eq_linear hL habs, abs_of_nonneg hx.1]

private theorem integral_exp_mul_squared_distance (r : ℝ) :
    (∫ x in 0..r, Real.exp (-2 * x) * (r - x) ^ 2) =
      (r ^ 2 - r + (1 - Real.exp (-2 * r)) / 2) / 2 := by
  let primitive (x : ℝ) := Real.exp (-2 * x) * (-(r - x) ^ 2 / 2 + (r - x) / 2 - 1 / 4)
  have hderiv (x : ℝ) :
      HasDerivAt primitive (Real.exp (-2 * x) * (r - x) ^ 2) x := by
    have hd := (hasDerivAt_const x r).sub (hasDerivAt_id x)
    have he := ((hasDerivAt_id x).const_mul (-2 : ℝ)).exp
    convert he.mul ((((hd.pow 2).neg.div_const 2).add (hd.div_const 2)).sub_const (1 / 4)) using 1
    · rfl
    · simp only [Pi.sub_apply, id_eq]
      norm_num
      ring
  have hc : Continuous (fun x : ℝ => Real.exp (-2 * x) * (r - x) ^ 2) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    (hc.intervalIntegrable _ _)]
  dsimp [primitive]
  rw [mul_zero, Real.exp_zero]
  ring

private theorem tent_energy_eq {a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L) :
    (∫ x : ℝ, Real.exp (-2 * |x|) * tent a L x ^ 2) =
      L ^ 2 * ((a / L) ^ 2 - a / L + (1 - Real.exp (-2 * (a / L))) / 2) := by
  have haL : L * (a / L) = a := by field_simp
  rw [tent_energy_eq_half ha hL]
  have hfactor (x : ℝ) : Real.exp (-2 * x) * (a - L * x) ^ 2 =
      L ^ 2 * (Real.exp (-2 * x) * (a / L - x) ^ 2) := by
    have hlinear : a - L * x = L * (a / L - x) := by rw [mul_sub, haL]
    rw [hlinear]
    ring
  simp_rw [hfactor]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_squared_distance]
  ring

/-- The sharp weighted energy bound and its attaining nonnegative profile. -/
theorem sharp_energy_bound {a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L) :
    (∀ f : ℝ → ℝ, f 0 = a → (∀ x, 0 ≤ f x) → (∀ x, a - L * |x| ≤ f x) →
      Integrable (fun x : ℝ => Real.exp (-2 * |x|) * f x ^ 2) →
      L ^ 2 * ((a / L) ^ 2 - a / L + (1 - Real.exp (-2 * (a / L))) / 2) ≤
        ∫ x : ℝ, Real.exp (-2 * |x|) * f x ^ 2) ∧
    (tent a L 0 = a ∧ (∀ x, 0 ≤ tent a L x) ∧ (∀ x, a - L * |x| ≤ tent a L x) ∧
      Integrable (fun x : ℝ => Real.exp (-2 * |x|) * tent a L x ^ 2) ∧
      (∫ x : ℝ, Real.exp (-2 * |x|) * tent a L x ^ 2) =
        L ^ 2 * ((a / L) ^ 2 - a / L + (1 - Real.exp (-2 * (a / L))) / 2)) := by
  have heq := tent_energy_eq ha hL
  refine ⟨?_, tent_at_zero ha L, fun _ => le_max_right _ _, fun _ => le_max_left _ _,
    tent_energy_integrable a hL, heq⟩
  intro f hf hn hp hi
  rw [← heq, ← hf]
  exact tent_energy_le f L hn (by simpa only [hf] using hp) hi hL

/-- The minimum exponential weight on the support of the tent gives a cubic bound. -/
theorem cube_le_exponential_energy (f : ℝ → ℝ) {L : ℝ} (hL : 0 < L)
    (hn : ∀ x, 0 ≤ f x) (hpeak : ∀ x, f 0 - L * |x| ≤ f x)
    (hi : Integrable (fun x : ℝ => Real.exp (-2 * |x|) * f x ^ 2)) :
    f 0 ^ 3 ≤ (3 / 2 * Real.exp (2 * (f 0 / L)) * L) *
      ∫ x : ℝ, Real.exp (-2 * |x|) * f x ^ 2 := by
  let r := f 0 / L
  have hr : 0 ≤ r := div_nonneg (hn 0) hL.le
  have hm : L * r = f 0 := by dsimp [r]; field_simp
  let C := Real.exp (-2 * r) * L ^ 2
  have hpolynomial : (∫ x in 0..r, C * (r - x) ^ 2) = C * (r ^ 3 / 3) := by
    rw [intervalIntegral.integral_const_mul]
    have hsub := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ 2)
      (a := 0) (b := r) r
    rw [sub_self, sub_zero] at hsub
    rw [hsub, integral_pow]
    ring
  have hleft : Continuous (fun x : ℝ => C * (r - x) ^ 2) := by fun_prop
  have hright : Continuous (fun x : ℝ => Real.exp (-2 * x) * (f 0 - L * x) ^ 2) := by
    fun_prop
  have hhalf : C * (r ^ 3 / 3) ≤ ∫ x in 0..r, Real.exp (-2 * x) * (f 0 - L * x) ^ 2 := by
    rw [← hpolynomial]
    refine intervalIntegral.integral_mono_on hr
      (hleft.intervalIntegrable _ _) (hright.intervalIntegrable _ _) ?_
    intro x hx
    have hlinear : f 0 - L * x = L * (r - x) := by rw [mul_sub, hm]
    rw [hlinear]
    calc
      C * (r - x) ^ 2 = Real.exp (-2 * r) * (L * (r - x)) ^ 2 := by dsimp [C]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hx.2]))
        (sq_nonneg _)
  have hwhole := mul_le_mul_of_nonneg_left hhalf (by norm_num : (0 : ℝ) ≤ 2)
  rw [← tent_energy_eq_half (hn 0) hL] at hwhole
  have hs := mul_le_mul_of_nonneg_left (hwhole.trans (tent_energy_le f L hn hpeak hi hL))
    (show 0 ≤ (3 / 2 : ℝ) * Real.exp (2 * r) * L by positivity)
  have hexp : Real.exp (2 * r) * Real.exp (-2 * r) = 1 := by
    rw [← Real.exp_add, show 2 * r + -2 * r = 0 by ring, Real.exp_zero]
  have hnormalize :
      (3 / 2 * Real.exp (2 * r) * L) * (2 * (C * (r ^ 3 / 3))) = f 0 ^ 3 := by
    calc
      _ = (Real.exp (2 * r) * Real.exp (-2 * r)) * (L * r) ^ 3 := by dsimp [C]; ring
      _ = _ := by rw [hexp, hm, one_mul]
  simpa only [hnormalize, r] using hs

end D5.S3.Fourier.Concentration.ExponentialTentEnergy

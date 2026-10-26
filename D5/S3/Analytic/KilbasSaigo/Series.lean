/- GID: D5/S3/Analytic/KilbasSaigo/Series
   generality: G
   mirror-B: D5/B/S3/Analytic/KilbasSaigo/Series
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics, mathlib/module/Mathlib.Analysis.Calculus.SmoothSeries]
   utility: none
   digest: Entire Kilbas–Saigo series and all of its differentiated series. -/

import D5.S3.Analytic.KilbasSaigo.Defs
import D5.S3.Analytic.KummerRatio.BetaIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.SmoothSeries

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Analytic.KilbasSaigo.Defs

noncomputable section
namespace D5.S3.Analytic.KilbasSaigo.Series

/-- The positive Gamma ratio with affine argument. -/
def phi (α m l s : ℝ) : ℝ :=
  Real.Gamma (1 + α * (l - m) + α * m * s + α) /
    Real.Gamma (1 + α * (l - m) + α * m * s)

/-- Coefficients of the signed derivative series. -/
def gCoeff (α m l : ℝ) (k n : ℕ) : ℝ :=
  ((n + k).factorial : ℝ) / (n.factorial : ℝ) * ksCoeff α m l (n + k)

/-- The signed derivatives on the negative real ray. -/
def g (α m l : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, gCoeff α m l k n * (-x) ^ n

/-- The strict parameter inequality makes the initial affine argument positive. -/
theorem base_pos {α m l : ℝ} (hα : 0 < α) (hl : m - 1 / α < l) :
    0 < 1 + α * (l - m) := by
  have h := (mul_lt_mul_of_pos_left hl hα)
  have hi : α * (1 / α) = 1 := by field_simp
  nlinarith

/-- The Gamma ratio is positive for every nonnegative index. -/
theorem phi_pos {α m l s : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) (hs : 0 ≤ s) : 0 < phi α m l s := by
  have ha := base_pos hα hl
  unfold phi
  apply div_pos <;> apply Real.Gamma_pos_of_pos <;> positivity

/-- The pinned coefficient product has the shifted Gamma-ratio recurrence. -/
theorem ksCoeff_succ (α m l : ℝ) (n : ℕ) :
    ksCoeff α m l (n + 1) = ksCoeff α m l n / phi α m l (n + 1) := by
  rw [ksCoeff, Finset.prod_range_succ]
  change ksCoeff α m l n * _ = _
  unfold phi
  have h0 : 1 + α * (l - m) + α * m * ((n : ℝ) + 1) =
      1 + α * ((n : ℝ) * m + l) := by ring
  have h1 : 1 + α * (l - m) + α * m * ((n : ℝ) + 1) + α =
      1 + α * ((n : ℝ) * m + l + 1) := by ring
  rw [h1, h0, div_div_eq_mul_div, mul_div_assoc]

/-- Every coefficient is strictly positive in the parameter range. -/
theorem ksCoeff_pos {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) (n : ℕ) : 0 < ksCoeff α m l n := by
  induction n with
  | zero => simp [ksCoeff]
  | succ n ih =>
    rw [ksCoeff_succ]
    exact div_pos ih (phi_pos hα hm hl (by positivity))

/-- The reciprocal Gamma ratio is a normalized beta integral. -/
theorem inv_phi_eq_beta {α m l s : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) (hs : 0 ≤ s) :
    1 / phi α m l s = (Real.Gamma α)⁻¹ *
      ∫ r in (0 : ℝ)..1, r ^ (1 + α * (l - m) + α * m * s - 1) *
        (1 - r) ^ (α - 1) := by
  have ha : 0 < 1 + α * (l - m) + α * m * s := by
    have := base_pos hα hl
    positivity
  rw [D5.S3.Analytic.KummerRatio.BetaIntegral.integral_beta ha hα]
  unfold phi
  have hg := (Real.Gamma_pos_of_pos hα).ne'
  field_simp

/-- The reciprocal Gamma ratio tends to zero along the natural indices. -/
theorem tendsto_inv_phi {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) :
    Tendsto (fun n : ℕ => 1 / phi α m l n) atTop (𝓝 0) := by
  let a := 1 + α * (l - m)
  let b := α * m
  let F : ℕ → ℝ → ℝ := fun n r => r ^ (a + b * n - 1) * (1 - r) ^ (α - 1)
  let w : ℝ → ℝ := fun r => r ^ (a - 1) * (1 - r) ^ (α - 1)
  have ha : 0 < a := base_pos hα hl
  have hb : 0 < b := mul_pos hα hm
  have hw : IntegrableOn w (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (D5.S3.Analytic.KummerRatio.BetaIntegral.intervalIntegrable_beta ha hα)
  have hlim : Tendsto (fun n => ∫ r in Ioo (0 : ℝ) 1, F n r) atTop (𝓝 0) := by
    convert tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioo 0 1))
      w (f := fun _ => (0 : ℝ)) ?_ hw ?_ ?_ using 1
    · simp
    · intro n
      apply Measurable.aestronglyMeasurable
      dsimp [F]
      fun_prop
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      have hr0 : 0 ≤ r := hr.1.le
      have hr1 : 0 ≤ 1 - r := sub_nonneg.mpr hr.2.le
      dsimp [F, w]
      rw [abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2.le
      have : 0 ≤ b * (n : ℝ) := by positivity
      linarith
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      have ht : Tendsto (fun n : ℕ => a + b * n - 1) atTop atTop := by
        convert tendsto_atTop_add_const_left atTop (a - 1)
          (tendsto_natCast_atTop_atTop.const_mul_atTop hb) using 1
        ext n
        ring
      have ht' := ((tendsto_rpow_atTop_of_base_lt_one r (by linarith [hr.1]) hr.2).comp ht).mul_const
        ((1 - r) ^ (α - 1))
      simpa [F] using ht'
  have hn (n : ℕ) : 1 / phi α m l n =
      (Real.Gamma α)⁻¹ * ∫ r in Ioo (0 : ℝ) 1, F n r := by
    rw [inv_phi_eq_beta hα hm hl (Nat.cast_nonneg n)]
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  simpa only [← hn, mul_zero] using hlim.const_mul (Real.Gamma α)⁻¹

/-- The derivative coefficients satisfy a ratio recurrence. -/
theorem gCoeff_succ (α m l : ℝ) (k n : ℕ) :
    gCoeff α m l k (n + 1) =
      (((n : ℝ) + k + 1) / (n + 1) / phi α m l (n + k + 1)) *
        gCoeff α m l k n := by
  have he : n + 1 + k = (n + k) + 1 := by omega
  simp only [gCoeff, he, ksCoeff_succ, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- The derivative of one monomial shifts the derivative coefficient. -/
theorem gCoeff_step (α m l : ℝ) (k n : ℕ) :
    ((n : ℝ) + 1) * gCoeff α m l k (n + 1) = gCoeff α m l (k + 1) n := by
  have he : n + 1 + k = n + (k + 1) := by omega
  simp only [gCoeff, he, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

private lemma summable_norm_gCoeff {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) (k : ℕ) (z : ℝ) :
    Summable (fun n => ‖gCoeff α m l k n * z ^ n‖) := by
  have ht := (tendsto_inv_phi hα hm hl).comp (tendsto_add_atTop_nat (k + 1))
  have hr := tendsto_add_mul_div_add_mul_atTop_nhds ((k : ℝ) + 1) 1 1
    (d := (1 : ℝ)) one_ne_zero
  simp only [one_mul, div_one] at hr
  have hq : Tendsto (fun n : ℕ =>
      (((n : ℝ) + k + 1) / (n + 1) / phi α m l (n + k + 1)) * z)
      atTop (𝓝 0) := by
    convert (hr.mul ht).mul_const z using 1
    · ext n
      simp only [Function.comp_def, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul]
      ring
    · simp
  have hqn : Tendsto (fun n : ℕ =>
      ‖(((n : ℝ) + k + 1) / (n + 1) / phi α m l (n + k + 1)) * z‖)
      atTop (𝓝 0) := by simpa using hq.norm
  apply summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num)
  filter_upwards [hqn.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
  simp only [norm_norm]
  rw [gCoeff_succ, pow_succ]
  have he :
      ((((n : ℝ) + k + 1) / (n + 1) / phi α m l (n + k + 1)) *
        gCoeff α m l k n) * (z ^ n * z) =
      ((((n : ℝ) + k + 1) / (n + 1) / phi α m l (n + k + 1)) * z) *
        (gCoeff α m l k n * z ^ n) := by ring
  rw [he, norm_mul]
  exact mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)

/-- All derivative coefficient series converge at every real argument. -/
theorem summable_gCoeff {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) (k : ℕ) (z : ℝ) :
    Summable (fun n => gCoeff α m l k n * z ^ n) :=
  (summable_norm_gCoeff hα hm hl k z).of_norm

/-- The defining Kilbas–Saigo series converges at every real argument. -/
theorem summable_kilbasSaigo {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) (z : ℝ) :
    Summable (fun n => ksCoeff α m l n * z ^ n) := by
  convert summable_gCoeff hα hm hl 0 z using 1
  funext n
  simp [gCoeff, (show (n.factorial : ℝ) ≠ 0 by positivity)]

/-- The derivative series at zero is its constant coefficient. -/
theorem g_zero (α m l : ℝ) (k : ℕ) :
    g α m l k 0 = (k.factorial : ℝ) * ksCoeff α m l k := by
  simp [g, gCoeff, zero_pow_eq]

/-- Every signed derivative has positive initial value. -/
theorem g_zero_pos {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) (k : ℕ) : 0 < g α m l k 0 := by
  rw [g_zero]
  exact mul_pos (by positivity) (ksCoeff_pos hα hm hl k)

/-- The original series on the negative ray is the zeroth derivative series. -/
theorem kilbasSaigo_neg_eq_g0 (α m l x : ℝ) :
    kilbasSaigo α m l (-x) = g α m l 0 x := by
  unfold kilbasSaigo g
  congr 1
  funext n
  simp [gCoeff, (show (n.factorial : ℝ) ≠ 0 by positivity)]

/-- The signed derivative series differentiate term by term on the whole real line. -/
theorem hasDerivAt_g {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) (k : ℕ) (x : ℝ) :
    HasDerivAt (g α m l k) (-g α m l (k + 1) x) x := by
  let R : ℝ := |x| + 1
  let F : ℕ → ℝ → ℝ := fun n y => gCoeff α m l k (n + 1) * (-y) ^ (n + 1)
  let F' : ℕ → ℝ → ℝ := fun n y => -gCoeff α m l (k + 1) n * (-y) ^ n
  let u : ℕ → ℝ := fun n => ‖gCoeff α m l (k + 1) n * R ^ n‖
  have hR : 0 < R := by dsimp [R]; positivity
  have hu : Summable u := summable_norm_gCoeff hα hm hl (k + 1) R
  have hd : ∀ n y, y ∈ Ioo (-R) R → HasDerivAt (F n) (F' n y) y := by
    intro n y hy
    have hterm : HasDerivAt (F n)
        (gCoeff α m l k (n + 1) * (((n : ℝ) + 1) * (-y) ^ n * (-1))) y := by
      simpa only [F, Pi.pow_apply, Pi.neg_apply, id_eq, Nat.cast_add, Nat.cast_one,
        Nat.add_sub_cancel] using
        ((((hasDerivAt_id y).neg).pow (n + 1)).const_mul (gCoeff α m l k (n + 1)))
    convert hterm using 1
    dsimp only [F']
    rw [← gCoeff_step α m l k n]
    ring
  have hb : ∀ n y, y ∈ Ioo (-R) R → ‖F' n y‖ ≤ u n := by
    intro n y hy
    have hyR : |y| ≤ R := abs_le.mpr ⟨by linarith [hy.1], hy.2.le⟩
    dsimp [F', u]
    simp only [abs_mul, abs_neg, abs_pow, abs_of_pos hR]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hyR n) (abs_nonneg _)
  have h0 : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
  have hx : x ∈ Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [le_abs_self x, neg_abs_le x]
  have hsum0 : Summable (fun n => F n 0) := by simp [F]
  have ht := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    hd hb h0 hsum0 hx
  have he : (fun y => gCoeff α m l k 0 + ∑' n, F n y) = g α m l k := by
    funext y
    simpa [g, F] using (summable_gCoeff hα hm hl k (-y)).tsum_eq_zero_add.symm
  have h := ht.const_add (gCoeff α m l k 0)
  rw [he] at h
  convert h using 1
  dsimp [F', g]
  rw [← tsum_neg]
  congr 1
  funext n
  ring

/-- Each derivative series is continuous on the real line. -/
theorem continuous_g {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) (k : ℕ) : Continuous (g α m l k) :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_g hα hm hl k x).continuousAt)

end D5.S3.Analytic.KilbasSaigo.Series

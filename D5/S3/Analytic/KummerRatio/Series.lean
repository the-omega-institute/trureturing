/- GID: D5/S3/Analytic/KummerRatio/Series
   generality: G
   mirror-B: D5/B/S3/Analytic/KummerRatio/Series
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Normed, mathlib/module/Mathlib.Analysis.Calculus.SmoothSeries]
   utility: none
   digest: Entire Kummer series, differential equation, positivity, and parameter recurrence. -/

import D5.S3.Analytic.KummerRatio.Defs
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.SmoothSeries

open Filter Topology
open D5.S3.Analytic.KummerRatio.Defs

namespace D5.S3.Analytic.KummerRatio.Series

private lemma coeff_zero (s c : ℝ) : kummerCoeff s c 0 = 1 := by
  simp [kummerCoeff]

private lemma coeff_succ (s : ℝ) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    kummerCoeff s c (n + 1) =
      ((s + n) / (c + n) / (n + 1)) * kummerCoeff s c n := by
  have hpc := (ascPochhammer_pos n c hc).ne'
  have hcn : c + (n : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  simp only [kummerCoeff, ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp

private lemma summable_norm_kummer (s c x : ℝ) (hc : 0 < c) :
    Summable (fun n => ‖kummerCoeff s c n * x ^ n‖) := by
  have hq : Tendsto (fun n : ℕ => ((s + n) / (c + n) / (n + 1)) * x)
      atTop (𝓝 0) := by
    have hr := tendsto_add_mul_div_add_mul_atTop_nhds s c (1 : ℝ) (d := 1) one_ne_zero
    simp only [one_mul, div_one] at hr
    simpa [div_eq_mul_inv] using
      (hr.mul tendsto_one_div_add_atTop_nhds_zero_nat).mul_const x
  apply summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num)
  have hqn : Tendsto (fun n : ℕ => ‖((s + n) / (c + n) / (n + 1)) * x‖) atTop (𝓝 0) := by
    simpa using hq.norm
  filter_upwards [hqn.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
  simp only [norm_norm]
  rw [coeff_succ s hc, pow_succ]
  have he : ((s + (n : ℝ)) / (c + n) / (n + 1) * kummerCoeff s c n) *
      (x ^ n * x) = (((s + n) / (c + n) / (n + 1)) * x) *
      (kummerCoeff s c n * x ^ n) := by ring
  rw [he, norm_mul]
  exact mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)

/-- The defining Kummer series converges for every real argument. -/
theorem summable_kummer (s c x : ℝ) (hc : 0 < c) :
    Summable (fun n => kummerCoeff s c n * x ^ n) :=
  (summable_norm_kummer s c x hc).of_norm

/-- The constant term gives the value at zero. -/
theorem kummer_zero (s c : ℝ) : kummer s c 0 = 1 := by
  simp [kummer, kummerCoeff, zero_pow_eq]

private lemma coeff_nonneg {s c : ℝ} (hs : 0 ≤ s) (hc : 0 < c) (n : ℕ) :
    0 ≤ kummerCoeff s c n := by
  apply div_nonneg _ (mul_nonneg (ascPochhammer_pos n c hc).le (by positivity))
  rcases hs.eq_or_lt with he | hp
  · rw [← he, ascPochhammer_eval_zero]
    split_ifs <;> norm_num
  · exact (ascPochhammer_pos n s hp).le

/-- Nonnegative coefficients bound the function below by its constant term. -/
theorem one_le_kummer {s c x : ℝ} (hs : 0 ≤ s) (hc : 0 < c) (hx : 0 ≤ x) :
    1 ≤ kummer s c x := by
  have h := (summable_kummer s c x hc).sum_le_tsum ({0} : Finset ℕ)
    (fun n _ => mul_nonneg (coeff_nonneg hs hc n) (pow_nonneg hx n))
  simpa [kummer, coeff_zero] using h

private lemma coeff_deriv (s : ℝ) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ((n : ℝ) + 1) * kummerCoeff s c (n + 1) =
      s / c * kummerCoeff (s + 1) (c + 1) n := by
  have hpc := (ascPochhammer_pos n (c + 1) (by linarith)).ne'
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hc0 := hc.ne'
  simp only [kummerCoeff, ascPochhammer_succ_left, Polynomial.eval_mul,
    Polynomial.eval_comp, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_one,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

private lemma kummer_tail (s : ℝ) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    kummer s c x = 1 + ∑' n : ℕ, kummerCoeff s c (n + 1) * x ^ (n + 1) := by
  simpa [kummer, coeff_zero] using (summable_kummer s c x hc).tsum_eq_zero_add

/-- Termwise differentiation of the entire Kummer series. -/
theorem hasDerivAt_kummer (s : ℝ) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivAt (kummer s c) (s / c * kummer (s + 1) (c + 1) x) x := by
  let R : ℝ := |x| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let g : ℕ → ℝ → ℝ := fun n y => kummerCoeff s c (n + 1) * y ^ (n + 1)
  let g' : ℕ → ℝ → ℝ := fun n y => s / c * kummerCoeff (s + 1) (c + 1) n * y ^ n
  let u : ℕ → ℝ := fun n => ‖s / c‖ * ‖kummerCoeff (s + 1) (c + 1) n * R ^ n‖
  have hu : Summable u := (summable_norm_kummer (s + 1) (c + 1) R (by linarith)).mul_left _
  have hd : ∀ n y, y ∈ Set.Ioo (-R) R → HasDerivAt (g n) (g' n y) y := by
    intro n y hy
    have ht : HasDerivAt (fun z : ℝ => kummerCoeff s c (n + 1) * z ^ (n + 1))
        (kummerCoeff s c (n + 1) * (((n + 1 : ℕ) : ℝ) * y ^ n)) y := by
      simpa only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, mul_one] using
        ((hasDerivAt_id y).pow (n + 1)).const_mul (kummerCoeff s c (n + 1))
    convert ht using 1
    dsimp [g']
    simp only [Nat.cast_add, Nat.cast_one]
    rw [← mul_assoc, mul_comm (kummerCoeff s c (n + 1)), coeff_deriv s hc]
  have hb : ∀ n y, y ∈ Set.Ioo (-R) R → ‖g' n y‖ ≤ u n := by
    intro n y hy
    have hyR : ‖y‖ ≤ R := by rw [Real.norm_eq_abs]; exact (abs_le.mpr ⟨by linarith [hy.1], hy.2.le⟩)
    dsimp [g', u]
    simp only [abs_mul, abs_pow, abs_of_pos hR]
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact pow_le_pow_left₀ (abs_nonneg _) hyR n
  have h0 : (0 : ℝ) ∈ Set.Ioo (-R) R := ⟨by linarith, hR⟩
  have hx : x ∈ Set.Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [le_abs_self x, neg_abs_le x]
  have hg0 : Summable (fun n => g n 0) := by
    simp [g]
  have ht := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    hd hb h0 hg0 hx
  have he : (fun y => 1 + ∑' n, g n y) = kummer s c := by
    ext y
    exact (kummer_tail s hc y).symm
  have h := ht.const_add 1
  rw [he] at h
  convert h using 1
  dsimp [g', kummer]
  simp_rw [mul_assoc]
  rw [tsum_mul_left]

/-- Kummer's function is continuous in its real argument. -/
theorem continuous_kummer (s : ℝ) {c : ℝ} (hc : 0 < c) : Continuous (kummer s c) :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_kummer s hc x).continuousAt)

private lemma pochhammer_shift (c : ℝ) (n : ℕ) :
    c * (ascPochhammer ℝ n).eval (c + 1) =
      (c + n) * (ascPochhammer ℝ n).eval c := by
  calc
    _ = (ascPochhammer ℝ (n + 1)).eval c := by
      simp [ascPochhammer_succ_left, Polynomial.eval_comp]
    _ = _ := by rw [ascPochhammer_succ_eval]; ring

private lemma coeff_lower_shift (s : ℝ) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    kummerCoeff s c (n + 1) = kummerCoeff s (c + 1) (n + 1) +
      s / (c * (c + 1)) * kummerCoeff (s + 1) (c + 2) n := by
  have hc0 := hc.ne'
  have hc1 : c + 1 ≠ 0 := by positivity
  have hp := (ascPochhammer_pos n c hc).ne'
  have hp1 := (ascPochhammer_pos n (c + 1) (by linarith)).ne'
  have hp2 := (ascPochhammer_pos n (c + 2) (by linarith)).ne'
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hcN : c + (n : ℝ) ≠ 0 := by positivity
  have hcN1 : c + 1 + (n : ℝ) ≠ 0 := by positivity
  have hrel1 := pochhammer_shift (c + 1) n
  have hrepl : (ascPochhammer ℝ n).eval (c + 2) =
      ((c + 1 + n) * (ascPochhammer ℝ n).eval (c + 1)) / (c + 1) := by
    apply (eq_div_iff hc1).mpr
    simpa only [show c + 1 + 1 = c + 2 by ring, mul_comm] using hrel1
  simp only [kummerCoeff, ascPochhammer_succ_left, Polynomial.eval_mul,
    Polynomial.eval_comp, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_one,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [show c + 1 + 1 = c + 2 by ring, hrepl]
  field_simp
  ring

/-- A contiguous relation shifting the lower parameter. -/
theorem kummer_contiguous (s : ℝ) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    kummer s c x = kummer s (c + 1) x +
      s * x / (c * (c + 1)) * kummer (s + 1) (c + 2) x := by
  rw [kummer_tail s hc, kummer_tail s (by linarith : 0 < c + 1)]
  have he : (fun n : ℕ => kummerCoeff s c (n + 1) * x ^ (n + 1)) =
      (fun n => kummerCoeff s (c + 1) (n + 1) * x ^ (n + 1) +
        (s * x / (c * (c + 1))) * (kummerCoeff (s + 1) (c + 2) n * x ^ n)) := by
    ext n
    rw [coeff_lower_shift s hc, pow_succ]
    ring
  have hsum1 := (summable_nat_add_iff 1).mpr (summable_kummer s (c + 1) x (by linarith))
  have hsum2 := (summable_kummer (s + 1) (c + 2) x (by linarith)).mul_left
    (s * x / (c * (c + 1)))
  rw [he, hsum1.tsum_add hsum2, tsum_mul_left]
  dsimp only [kummer]
  ring

private lemma coeff_ode (s : ℝ) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    s / c * ((s + 1) / (c + 1) * kummerCoeff (s + 2) (c + 2) n) +
      c * (s / c * kummerCoeff (s + 1) (c + 1) (n + 1)) -
      s / c * kummerCoeff (s + 1) (c + 1) n - s * kummerCoeff s c (n + 1) = 0 := by
  have hd := coeff_deriv (s + 1) (by linarith : 0 < c + 1) n
  have hd0 := coeff_deriv s hc n
  have hr := coeff_succ (s + 1) (by linarith : 0 < c + 1) n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hcn : c + 1 + (n : ℝ) ≠ 0 := by positivity
  have hs2 : s + 1 + 1 = s + 2 := by ring
  have hc2 : c + 1 + 1 = c + 2 := by ring
  rw [hs2, hc2] at hd
  rw [← hd, hr]
  have hk : kummerCoeff s c (n + 1) =
      (s / c * kummerCoeff (s + 1) (c + 1) n) / (n + 1) := by
    exact (eq_div_iff hn).mpr (by nlinarith [hd0])
  rw [hk]
  field_simp
  ring

/-- Kummer's differential equation with both derivatives written as shifted series. -/
theorem kummer_ode (s : ℝ) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    x * (s / c * ((s + 1) / (c + 1) * kummer (s + 2) (c + 2) x)) +
      (c - x) * (s / c * kummer (s + 1) (c + 1) x) - s * kummer s c x = 0 := by
  have htail (t d : ℝ) (hd : 0 < d) :
      HasSum (fun n : ℕ => kummerCoeff t d (n + 1) * x ^ (n + 1)) (kummer t d x - 1) := by
    have h := ((summable_nat_add_iff 1).mpr (summable_kummer t d x hd)).hasSum
    convert h using 1
    rw [kummer_tail t hd x]
    ring
  have h2 := (summable_kummer (s + 2) (c + 2) x (by linarith)).hasSum
  have h1 := (summable_kummer (s + 1) (c + 1) x (by linarith)).hasSum
  have h1t := htail (s + 1) (c + 1) (by linarith)
  have h0t := htail s c hc
  have H := (((h2.mul_left ((s + 1) / (c + 1))).mul_left (s / c)).mul_left x).add
    ((h1t.mul_left (s / c)).mul_left c)
  have H := (H.sub ((h1.mul_left (s / c)).mul_left x)).sub (h0t.mul_left s)
  have Hz : HasSum (fun _ : ℕ => (0 : ℝ))
      (x * (s / c * ((s + 1) / (c + 1) * kummer (s + 2) (c + 2) x)) +
        c * (s / c * (kummer (s + 1) (c + 1) x - 1)) -
        x * (s / c * kummer (s + 1) (c + 1) x) - s * (kummer s c x - 1)) := by
    convert H using 1
    · ext n
      have he := congrArg (fun z : ℝ => z * x ^ (n + 1)) (coeff_ode s hc n)
      rw [pow_succ] at he
      simp only [pow_succ]
      convert he.symm using 1 <;> ring
    · rfl
  have he := Hz.unique hasSum_zero
  have hc0 := hc.ne'
  field_simp at he ⊢
  linear_combination he

end D5.S3.Analytic.KummerRatio.Series

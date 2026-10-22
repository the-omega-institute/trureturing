/- GID: D5/S3/Analytic/BesselRedheffer/Series
   generality: G
   mirror-B: D5/B/S3/Analytic/BesselRedheffer/Series
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Normed, mathlib/module/Mathlib.Analysis.Calculus.SmoothSeries, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Pow]
   utility: none
   digest: Convergence, differentiation, continuity, and the normalized Bessel equation. -/

import D5.S3.Analytic.BesselRedheffer.Defs
import D5.S3.Analytic.KummerRatio.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow

open Filter Topology
open D5.S3.Analytic.BesselRedheffer.Defs

set_option maxHeartbeats 800000

namespace D5.S3.Analytic.BesselRedheffer.Series

private noncomputable def coeff (b : ℝ) (n : ℕ) : ℝ :=
  1 / ((n.factorial : ℝ) * (ascPochhammer ℝ n).eval b)

private lemma coeff_zero (b : ℝ) : coeff b 0 = 1 := by simp [coeff]

private lemma coeff_succ {b : ℝ} (hb : 0 < b) (n : ℕ) :
    coeff b (n + 1) = (1 / (b + n) / (n + 1)) * coeff b n := by
  have hp := (ascPochhammer_pos n b hb).ne'
  have hbn : b + (n : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  simp only [coeff, ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp

private lemma summable_norm_series {b : ℝ} (hb : 0 < b) (t : ℝ) :
    Summable (fun n => ‖coeff b n * t ^ n‖) := by
  have hi : Tendsto (fun n : ℕ => 1 / (b + (n : ℝ))) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_left atTop b tendsto_natCast_atTop_atTop)
  have hq : Tendsto (fun n : ℕ => (1 / (b + n) / (n + 1)) * t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_div, one_mul, zero_mul] using
      (hi.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).mul_const t
  apply summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num)
  have hqn : Tendsto (fun n : ℕ => ‖(1 / (b + n) / (n + 1)) * t‖) atTop (𝓝 0) := by
    simpa using hq.norm
  filter_upwards [hqn.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
  simp only [norm_norm]
  rw [coeff_succ hb, pow_succ]
  have he : ((1 / (b + (n : ℝ)) / (n + 1)) * coeff b n) * (t ^ n * t) =
      ((1 / (b + n) / (n + 1)) * t) * (coeff b n * t ^ n) := by ring
  rw [he, norm_mul]
  exact mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)

/-- Absolute convergence of the defining normalized Bessel series. -/
theorem summable_nbessel {ν : ℝ} (hν : -1 < ν) (x : ℝ) :
    Summable (fun k : ℕ => (-(x ^ 2) / 4) ^ k /
      ((k.factorial : ℝ) * (ascPochhammer ℝ k).eval (ν + 1))) := by
  have hh : Summable (fun n => coeff (ν + 1) n * (-(x ^ 2) / 4) ^ n) :=
    (summable_norm_series (by linarith : 0 < ν + 1) (-(x ^ 2) / 4)).of_norm
  convert hh using 1
  ext n
  dsimp only [coeff]
  ring

/-- The normalized Bessel series takes the value one at zero. -/
theorem nbessel_zero (ν : ℝ) : nbessel ν 0 = 1 := by
  rw [nbessel, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

private noncomputable def entire (b t : ℝ) : ℝ := ∑' n : ℕ, coeff b n * t ^ n

private lemma coeff_deriv {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ((n : ℝ) + 1) * coeff b (n + 1) = 1 / b * coeff (b + 1) n := by
  have hp := (ascPochhammer_pos n (b + 1) (by linarith)).ne'
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hb0 := hb.ne'
  simp only [coeff, ascPochhammer_succ_left, Polynomial.eval_mul,
    Polynomial.eval_comp, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_one,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

private lemma entire_tail {b : ℝ} (hb : 0 < b) (t : ℝ) :
    entire b t = 1 + ∑' n : ℕ, coeff b (n + 1) * t ^ (n + 1) := by
  simpa [entire, coeff_zero] using (summable_norm_series hb t).of_norm.tsum_eq_zero_add

private lemma hasDerivAt_entire {b : ℝ} (hb : 0 < b) (t : ℝ) :
    HasDerivAt (entire b) (1 / b * entire (b + 1) t) t := by
  let R : ℝ := |t| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let g : ℕ → ℝ → ℝ := fun n y => coeff b (n + 1) * y ^ (n + 1)
  let g' : ℕ → ℝ → ℝ := fun n y => 1 / b * coeff (b + 1) n * y ^ n
  let u : ℕ → ℝ := fun n => ‖1 / b‖ * ‖coeff (b + 1) n * R ^ n‖
  have hu : Summable u := (summable_norm_series (by linarith : 0 < b + 1) R).mul_left _
  have hd : ∀ n y, y ∈ Set.Ioo (-R) R → HasDerivAt (g n) (g' n y) y := by
    intro n y hy
    have ht : HasDerivAt (fun z : ℝ => coeff b (n + 1) * z ^ (n + 1))
        (coeff b (n + 1) * (((n + 1 : ℕ) : ℝ) * y ^ n)) y := by
      simpa only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, mul_one] using
        ((hasDerivAt_id y).pow (n + 1)).const_mul (coeff b (n + 1))
    convert ht using 1
    dsimp [g']
    simp only [Nat.cast_add, Nat.cast_one]
    rw [← mul_assoc, mul_comm (coeff b (n + 1)), coeff_deriv hb]
  have hbnd : ∀ n y, y ∈ Set.Ioo (-R) R → ‖g' n y‖ ≤ u n := by
    intro n y hy
    have hyR : ‖y‖ ≤ R := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hy.1], hy.2.le⟩
    dsimp [g', u]
    simp only [abs_mul, abs_pow, abs_of_pos hR]
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact pow_le_pow_left₀ (abs_nonneg _) hyR n
  have h0 : (0 : ℝ) ∈ Set.Ioo (-R) R := ⟨by linarith, hR⟩
  have ht : t ∈ Set.Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [le_abs_self t, neg_abs_le t]
  have hg0 : Summable (fun n => g n 0) := by simp [g]
  have hd := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    hd hbnd h0 hg0 ht
  have he : (fun y => 1 + ∑' n, g n y) = entire b := by
    ext y
    exact (entire_tail hb y).symm
  have h := hd.const_add 1
  rw [he] at h
  convert h using 1
  dsimp [g', entire]
  simp_rw [mul_assoc]
  rw [tsum_mul_left]

private lemma nbessel_eq_entire (ν x : ℝ) :
    nbessel ν x = entire (ν + 1) (-(x ^ 2) / 4) := by
  apply tsum_congr
  intro n
  simp only [coeff, div_eq_mul_inv, mul_comm, one_mul]

/-- Differentiation shifts the order by one. -/
theorem hasDerivAt_nbessel {ν : ℝ} (hν : -1 < ν) (x : ℝ) :
    HasDerivAt (nbessel ν) (-x / (2 * (ν + 1)) * nbessel (ν + 1) x) x := by
  have hg : HasDerivAt (fun y : ℝ => -(y ^ 2) / 4) (-x / 2) x := by
    convert (((hasDerivAt_id x).pow 2).neg.div_const 4) using 1 <;> simp <;> ring
  have hh := (hasDerivAt_entire (by linarith : 0 < ν + 1) (-(x ^ 2) / 4)).comp x hg
  simp only [Function.comp_def] at hh
  simp_rw [← nbessel_eq_entire] at hh
  convert hh using 1
  rw [nbessel_eq_entire (ν + 1)]
  have hν0 : ν + 1 ≠ 0 := by linarith
  field_simp
  <;> ring

/-- The normalized Bessel function is continuous on the real line. -/
theorem continuous_nbessel {ν : ℝ} (hν : -1 < ν) : Continuous (nbessel ν) :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_nbessel hν x).continuousAt)

/-- Positivity holds throughout a neighbourhood of the origin. -/
theorem nbessel_pos_near_zero {ν : ℝ} (hν : -1 < ν) :
    ∀ᶠ x in 𝓝 (0 : ℝ), 0 < nbessel ν x := by
  have h : (0 : ℝ) < nbessel ν 0 := by rw [nbessel_zero]; norm_num
  exact (continuous_nbessel hν).continuousAt.eventually (lt_mem_nhds h)

private lemma coeff_lower_shift {b : ℝ} (hb : 0 < b) (n : ℕ) :
    coeff b (n + 1) = coeff (b + 1) (n + 1) +
      1 / (b * (b + 1)) * coeff (b + 2) n := by
  have hb0 := hb.ne'
  have hb1 : b + 1 ≠ 0 := by positivity
  have hp := (ascPochhammer_pos n b hb).ne'
  have hp1 := (ascPochhammer_pos n (b + 1) (by linarith)).ne'
  have hp2 := (ascPochhammer_pos n (b + 2) (by linarith)).ne'
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hbn : b + (n : ℝ) ≠ 0 := by positivity
  have hbn1 : b + 1 + (n : ℝ) ≠ 0 := by positivity
  have hrel := D5.S3.Analytic.KummerRatio.Series.pochhammer_shift (b + 1) n
  have hrepl : (ascPochhammer ℝ n).eval (b + 2) =
      ((b + 1 + n) * (ascPochhammer ℝ n).eval (b + 1)) / (b + 1) := by
    apply (eq_div_iff hb1).mpr
    simpa only [show b + 1 + 1 = b + 2 by ring, mul_comm] using hrel
  simp only [coeff, ascPochhammer_succ_left, Polynomial.eval_mul,
    Polynomial.eval_comp, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_one,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [show b + 1 + 1 = b + 2 by ring, hrepl]
  field_simp
  ring

private lemma entire_contiguous {b : ℝ} (hb : 0 < b) (t : ℝ) :
    entire b t = entire (b + 1) t + t / (b * (b + 1)) * entire (b + 2) t := by
  rw [entire_tail hb, entire_tail (by linarith : 0 < b + 1)]
  have he : (fun n : ℕ => coeff b (n + 1) * t ^ (n + 1)) =
      (fun n => coeff (b + 1) (n + 1) * t ^ (n + 1) +
        t / (b * (b + 1)) * (coeff (b + 2) n * t ^ n)) := by
    ext n
    rw [coeff_lower_shift hb, pow_succ]
    ring
  have hs1 := (summable_nat_add_iff 1).mpr (summable_norm_series (by linarith : 0 < b + 1) t).of_norm
  have hs2 := (summable_norm_series (by linarith : 0 < b + 2) t).of_norm.mul_left
    (t / (b * (b + 1)))
  rw [he, hs1.tsum_add hs2, tsum_mul_left]
  dsimp only [entire]
  ring

/-- A contiguous relation for three consecutive orders. -/
theorem nbessel_contiguous {ν : ℝ} (hν : -1 < ν) (x : ℝ) :
    nbessel ν x = nbessel (ν + 1) x -
      x ^ 2 / (4 * (ν + 1) * (ν + 2)) * nbessel (ν + 2) x := by
  simp_rw [nbessel_eq_entire]
  have he := entire_contiguous (by linarith : 0 < ν + 1) (-(x ^ 2) / 4)
  rw [show ν + 1 + 1 = ν + 2 by ring, show ν + 1 + 2 = ν + 2 + 1 by ring] at he
  convert he using 1 <;> field_simp <;> ring

/-- The derivative of the first derivative, in shifted-series form. -/
theorem hasDerivAt_nbessel_deriv {ν : ℝ} (hν : -1 < ν) (x : ℝ) :
    HasDerivAt (fun y => -y / (2 * (ν + 1)) * nbessel (ν + 1) y)
      (-1 / (2 * (ν + 1)) * nbessel (ν + 1) x +
        x ^ 2 / (4 * (ν + 1) * (ν + 2)) * nbessel (ν + 2) x) x := by
  have hd := (((hasDerivAt_id x).neg.div_const (2 * (ν + 1))).mul
    (hasDerivAt_nbessel (by linarith : -1 < ν + 1) x))
  convert hd using 1
  · rfl
  · simp only [Pi.neg_apply, id_eq]
    rw [show ν + 1 + 1 = ν + 2 by ring]
    field_simp
    <;> ring

/-- The Bessel differential equation, multiplied by its argument. -/
theorem nbessel_ode {ν : ℝ} (hν : -1 < ν) (x : ℝ) :
    x * (-1 / (2 * (ν + 1)) * nbessel (ν + 1) x +
      x ^ 2 / (4 * (ν + 1) * (ν + 2)) * nbessel (ν + 2) x) +
    (2 * ν + 1) * (-x / (2 * (ν + 1)) * nbessel (ν + 1) x) +
    x * nbessel ν x = 0 := by
  rw [nbessel_contiguous hν x]
  have hν0 : ν + 1 ≠ 0 := by linarith
  field_simp
  <;> ring

end D5.S3.Analytic.BesselRedheffer.Series

/- GID: D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis
   generality: I
   mirror-B: D5/B/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Group.ForwardDiff, mathlib/module/Mathlib.Analysis.Analytic.Order, mathlib/module/Mathlib.Analysis.Complex.TaylorSeries, mathlib/module/Mathlib.Analysis.Complex.RealDeriv]
   utility: none
   digest: Finite binomial moments and imaginary-axis bounds for analytic positive definite functions. -/

import D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.RealDeriv

/-! Binomial tests of finite positive semidefinite kernels and analytic continuation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Finset Filter Complex
open scoped BigOperators Topology

namespace D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis

private def weight (k j : ℕ) : ℝ := (-1) ^ j * k.choose j

private lemma weighted_shift (k : ℕ) (g : ℝ → ℝ) (x : ℝ) :
    ∑ j ∈ range (k + 1), weight k j * g (x + j) =
      (-1) ^ k * (fwdDiff (1 : ℝ))^[k] g x := by
  rw [fwdDiff_iter_eq_sum_shift, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by simpa using hj
  have hs : (-1 : ℝ) ^ k * (-1) ^ (k - j) = (-1) ^ j := by
    have he : k + (k - j) = j + 2 * (k - j) := by omega
    rw [← pow_add, he, pow_add, pow_mul]
    norm_num
  simp only [weight, zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast, nsmul_eq_mul, mul_one]
  rw [← mul_assoc, ← mul_assoc, hs]

private lemma double_weighted_shift (k : ℕ) (g : ℝ → ℝ) :
    ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
      weight k i * weight k j * g ((i : ℝ) - j) =
      (-1) ^ k * (fwdDiff (1 : ℝ))^[2 * k] g (-(k : ℝ)) := by
  have hi (i : ℕ) :
      ∑ j ∈ range (k + 1), weight k j * g ((i : ℝ) - j) =
        (fwdDiff (1 : ℝ))^[k] g ((i : ℝ) - k) := by
    rw [← sum_range_reflect]
    have he : ∀ j ∈ range (k + 1),
        weight k (k + 1 - 1 - j) * g ((i : ℝ) - ((k + 1 - 1 - j : ℕ) : ℝ)) =
          ((-1 : ℤ) ^ (k - j) * k.choose j) • g ((i : ℝ) - k + j • (1 : ℝ)) := by
      intro j hj
      have hjk : j ≤ k := by simpa using hj
      simp only [Nat.add_sub_cancel, weight, Nat.choose_symm hjk,
        zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
        Int.cast_natCast, nsmul_eq_mul, mul_one]
      rw [Nat.cast_sub hjk]
      congr 2
      ring
    rw [sum_congr rfl he]
    exact (fwdDiff_iter_eq_sum_shift 1 g k ((i : ℝ) - k)).symm
  simp_rw [mul_assoc, ← mul_sum, hi]
  have he : (fun i : ℕ => weight k i * (fwdDiff (1 : ℝ))^[k] g ((i : ℝ) - k)) =
      fun i => weight k i * (fwdDiff (1 : ℝ))^[k] g (-(k : ℝ) + i) := by
    ext i
    congr 1
    ring
  rw [he, weighted_shift]
  congr 1
  rw [show 2 * k = k + k by omega, Function.iterate_add_apply]

/-- The binomial quadratic moment vanishes below order `2k`, with its exact
first surviving value at order `2k`. -/
theorem finite_difference_moment (k m : ℕ) (hm : m ≤ 2 * k) :
    (∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
      ((-1 : ℝ) ^ i * k.choose i) * ((-1 : ℝ) ^ j * k.choose j) *
        ((i : ℝ) - j) ^ m) =
      if m = 2 * k then (-1 : ℝ) ^ k * (2 * k).factorial else 0 := by
  change (∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
    weight k i * weight k j * (fun x : ℝ => x ^ m) ((i : ℝ) - j)) = _
  rw [double_weighted_shift k (fun x : ℝ => x ^ m)]
  split_ifs with he
  · subst m
    rw [fwdDiff_iter_eq_factorial]
    rfl
  · rw [fwdDiff_iter_pow_eq_zero_of_lt (lt_of_le_of_ne hm he)]
    simp

private lemma quadratic_nonneg {f : ℝ → ℂ}
    (hf : D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion.PositiveDefinite f)
    (k : ℕ) (h : ℝ) :
    0 ≤ ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
      weight k i * weight k j * (f (((i : ℝ) - j) * h)).re := by
  have H := (hf (k + 1) (fun i => -(i : ℝ) * h)).re_dotProduct_nonneg
    (fun i => (weight k i : ℂ))
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Complex.star_def,
    Complex.conj_ofReal] at H
  change 0 ≤ (∑ i : Fin (k + 1), (weight k i : ℂ) *
    ∑ j : Fin (k + 1), f (-((j : ℕ) : ℝ) * h - -((i : ℕ) : ℝ) * h) *
      (weight k j : ℂ)).re at H
  simp only [mul_sum, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero] at H
  simp only [Finset.sum_range]
  convert H using 1
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [show -((j : ℕ) : ℝ) * h - -((i : ℕ) : ℝ) * h =
      (((i : ℕ) : ℝ) - j) * h by ring]
  ring

private lemma moment_expansion (k N : ℕ) (g H : ℝ → ℝ) (a : ℕ → ℝ) (h : ℝ)
    (E : ∀ x, g x = (∑ m ∈ range N, a m * x ^ m) + x ^ N * H x) :
    (∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
      weight k i * weight k j * g (((i : ℝ) - j) * h)) =
      (∑ m ∈ range N, a m * h ^ m *
        (∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
          weight k i * weight k j * ((i : ℝ) - j) ^ m)) +
        h ^ N * (∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
          weight k i * weight k j * ((i : ℝ) - j) ^ N * H (((i : ℝ) - j) * h)) := by
  simp_rw [E, mul_add, sum_add_distrib]
  congr 1
  · simp_rw [mul_sum]
    conv_lhs =>
      arg 2
      ext i
      rw [sum_comm]
    rw [sum_comm]
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [mul_pow]
    ring
  · simp_rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [mul_pow]
    ring

private lemma even_taylor_nonneg {f : ℝ → ℂ}
    (hf : D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion.PositiveDefinite f)
    {g : ℝ → ℝ} (hg : AnalyticAt ℝ g 0)
    (hgf : ∀ᶠ x in 𝓝 0, g x = (f x).re) (k : ℕ) :
    0 ≤ (-1 : ℝ) ^ k * (iteratedDeriv (2 * k) g 0 / (2 * k).factorial) := by
  classical
  let a : ℕ → ℝ := fun m => iteratedDeriv m g 0 / m.factorial
  obtain ⟨H, hH, hE⟩ := hg.exists_eq_sum_add_pow_mul (2 * k + 1)
  have E (x : ℝ) : g x = (∑ m ∈ range (2 * k + 1), a m * x ^ m) +
      x ^ (2 * k + 1) * H x := by
    rw [hE x]
    congr 1
    apply sum_congr rfl
    intro m hm
    dsimp [a]
    ring
  let B : ℝ → ℝ := fun h => ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
    weight k i * weight k j * ((i : ℝ) - j) ^ (2 * k + 1) * H (((i : ℝ) - j) * h)
  have hB : ContinuousAt B 0 := by
    dsimp [B, ContinuousAt]
    apply tendsto_finsetSum
    intro i hi
    apply tendsto_finsetSum
    intro j hj
    have ht : Tendsto (fun h : ℝ => ((i : ℝ) - j) * h) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).const_mul
        ((i : ℝ) - j)
    simpa only [mul_zero, Function.comp_def] using tendsto_const_nhds.mul (hH.continuousAt.tendsto.comp ht)
  have EQ (h : ℝ) :
      (∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
        weight k i * weight k j * g (((i : ℝ) - j) * h)) =
      h ^ (2 * k) * ((-1 : ℝ) ^ k * a (2 * k) * (2 * k).factorial + h * B h) := by
    rw [moment_expansion k (2 * k + 1) g H a h E]
    have hm : (∑ m ∈ range (2 * k + 1), a m * h ^ m *
        (∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
          weight k i * weight k j * ((i : ℝ) - j) ^ m)) =
        a (2 * k) * h ^ (2 * k) * ((-1 : ℝ) ^ k * (2 * k).factorial) := by
      calc
        _ = ∑ m ∈ range (2 * k + 1), a m * h ^ m *
            (if m = 2 * k then (-1 : ℝ) ^ k * (2 * k).factorial else 0) := by
          apply sum_congr rfl
          intro m hm
          rw [show (∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
            weight k i * weight k j * ((i : ℝ) - j) ^ m) =
            if m = 2 * k then (-1 : ℝ) ^ k * (2 * k).factorial else 0 from
              finite_difference_moment k m (by simpa using hm)]
        _ = _ := by simp
    rw [hm, pow_succ]
    change _ = _ * (_ + h * B h)
    dsimp only [B]
    ring
  have hnonneg : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      0 ≤ (-1 : ℝ) ^ k * a (2 * k) * (2 * k).factorial + h * B h := by
    have hlocal : ∀ᶠ h in 𝓝 (0 : ℝ), ∀ i ∈ range (k + 1), ∀ j ∈ range (k + 1),
        g (((i : ℝ) - j) * h) = (f (((i : ℝ) - j) * h)).re := by
      apply (eventually_all_finset (range (k + 1))).mpr
      intro i hi
      apply (eventually_all_finset (range (k + 1))).mpr
      intro j hj
      have ht : Tendsto (fun h : ℝ => ((i : ℝ) - j) * h) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).const_mul
          ((i : ℝ) - j)
      exact Filter.EventuallyEq.comp_tendsto hgf ht
    filter_upwards [hlocal.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with h he hh
    have hQ := quadratic_nonneg hf k h
    have hge : 0 ≤ ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
        weight k i * weight k j * g (((i : ℝ) - j) * h) := by
      convert hQ using 1
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      rw [he i hi j hj]
    rw [EQ] at hge
    exact nonneg_of_mul_nonneg_right hge (pow_pos hh (2 * k))
  have hlim : Tendsto (fun h : ℝ => (-1 : ℝ) ^ k * a (2 * k) * (2 * k).factorial + h * B h)
      (𝓝[>] 0) (𝓝 ((-1 : ℝ) ^ k * a (2 * k) * (2 * k).factorial)) := by
    have hc : ContinuousAt (fun h : ℝ =>
        (-1 : ℝ) ^ k * a (2 * k) * (2 * k).factorial + h * B h) 0 :=
      continuousAt_const.add (continuousAt_id.mul hB)
    simpa only [zero_mul, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hh := ge_of_tendsto hlim hnonneg
  exact nonneg_of_mul_nonneg_left hh (by positivity : (0 : ℝ) < (2 * k).factorial)

private lemma real_taylor_data {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hreal : ∀ᶠ x : ℝ in 𝓝 0, (F x).im = 0) :
    AnalyticAt ℝ (fun x : ℝ => (F x).re) 0 ∧
    ∀ n, (iteratedDeriv n F 0 / (n.factorial : ℂ)).im = 0 ∧
      (iteratedDeriv n F 0 / (n.factorial : ℂ)).re =
        iteratedDeriv n (fun x : ℝ => (F x).re) 0 / n.factorial := by
  let a : ℕ → ℂ := fun n => iteratedDeriv n F 0 / n.factorial
  obtain ⟨r, hp⟩ := hF.hasFPowerSeriesAt
  have hp' : HasFPowerSeriesOnBall F
      ((FormalMultilinearSeries.ofScalars ℂ a).restrictScalars ℝ)
      (Complex.ofRealCLM (0 : ℝ)) r := by
    simpa [a] using hp.restrictScalars (𝕜 := ℝ)
  have hr := Complex.reCLM.comp_hasFPowerSeriesOnBall
    (hp'.compContinuousLinearMap (u := Complex.ofRealCLM))
  have hi := Complex.imCLM.comp_hasFPowerSeriesOnBall
    (hp'.compContinuousLinearMap (u := Complex.ofRealCLM))
  have ha : AnalyticAt ℝ (fun x : ℝ => (F x).re) 0 := hr.analyticAt
  refine ⟨ha, fun n => ?_⟩
  have hz := hi.hasFPowerSeriesAt.eq_zero_of_eventually hreal
  have he := hr.hasFPowerSeriesAt.eq_formalMultilinearSeries ha.hasFPowerSeriesAt
  have hz' := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p n (fun _ => 1)) hz
  have he' := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p n (fun _ => 1)) he
  have hc (n : ℕ) :
      (((FormalMultilinearSeries.ofScalars ℂ a).restrictScalars ℝ).compContinuousLinearMap
        Complex.ofRealCLM).coeff n = a n := by
    change FormalMultilinearSeries.ofScalars ℂ a n (fun _ => 1) = a n
    simp [FormalMultilinearSeries.ofScalars_apply_eq]
  constructor
  · change ((((FormalMultilinearSeries.ofScalars ℂ a).restrictScalars ℝ).compContinuousLinearMap
        Complex.ofRealCLM).coeff n).im = 0 at hz'
    simpa only [hc, a] using hz'
  · change ((((FormalMultilinearSeries.ofScalars ℂ a).restrictScalars ℝ).compContinuousLinearMap
        Complex.ofRealCLM).coeff n).re = _ at he'
    simpa only [hc, FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul,
      mul_one, a] using he'

/-- An analytic extension of a real positive definite function cannot decrease
from its value at zero along the imaginary radius of its disk. -/
theorem le_re_of_positiveDefinite {f : ℝ → ℂ}
    (hf : D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion.PositiveDefinite f)
    (hreal : ∀ x, (f x).im = 0) {F : ℂ → ℂ} {R : ℝ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 R))
    (hFf : ∀ x : ℝ, |x| < R → F x = f x) {y : ℝ}
    (hy0 : 0 ≤ y) (hyR : y < R) :
    (f 0).re ≤ (F (y * Complex.I)).re := by
  classical
  have hR : 0 < R := hy0.trans_lt hyR
  have hFa : AnalyticAt ℂ F 0 := hF.analyticAt (Metric.ball_mem_nhds 0 hR)
  have hlocal : ∀ᶠ x : ℝ in 𝓝 0, F x = f x := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hR] with x hx
    exact hFf x (by simpa [Real.dist_eq] using hx)
  obtain ⟨hgreal, hcoef⟩ := real_taylor_data hFa
    (hlocal.mono (fun x hx => hx ▸ hreal x))
  have ha (k : ℕ) : 0 ≤ (-1 : ℝ) ^ k *
      (iteratedDeriv (2 * k) F 0 / ((2 * k).factorial : ℂ)).re := by
    rw [(hcoef _).2]
    exact even_taylor_nonneg hf hgreal (hlocal.mono (fun _ hx => congrArg Complex.re hx)) k
  have hz : (y : ℂ) * Complex.I ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, dist_zero_right, norm_mul, Real.norm_eq_abs, abs_of_nonneg hy0]
      using hyR
  have hs := Complex.hasSum_re (Complex.hasSum_taylorSeries_on_ball hF hz)
  have hterm (n : ℕ) (hn : n ≠ 0) : 0 ≤
      (((n.factorial : ℂ)⁻¹ • ((y : ℂ) * Complex.I - 0) ^ n • iteratedDeriv n F 0) : ℂ).re := by
    let a : ℂ := iteratedDeriv n F 0 / n.factorial
    have har : (a.re : ℂ) = a := Complex.ext (by simp) (by exact (hcoef n).1.symm)
    have he : ((n.factorial : ℂ)⁻¹ • ((y : ℂ) * Complex.I - 0) ^ n •
        iteratedDeriv n F 0 : ℂ) = a * ((y : ℂ) * Complex.I) ^ n := by
      dsimp [a]
      simp only [smul_eq_mul, sub_zero, div_eq_mul_inv]
      ring
    rw [he, ← har, mul_pow, ← Complex.ofReal_pow]
    rcases Nat.even_or_odd n with heven | hodd
    · obtain ⟨k, hk⟩ := heven
      have hn' : n = 2 * k := by omega
      have hI : Complex.I ^ n = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by
        rw [hn', pow_mul, Complex.I_sq]
        norm_cast
      rw [hI, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
      have hk : 0 ≤ (-1 : ℝ) ^ k * a.re := by simpa only [a, hn'] using ha k
      nlinarith [mul_nonneg hk (pow_nonneg hy0 n)]
    · obtain ⟨k, hk⟩ := hodd
      have hn' : n = 2 * k + 1 := by omega
      have hI : Complex.I ^ n = (((-1 : ℝ) ^ k : ℝ) : ℂ) * Complex.I := by
        rw [hn', pow_succ, pow_mul, Complex.I_sq]
        norm_cast
      rw [hI, ← mul_assoc, ← Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_mul]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, le_refl]
  have hb := sum_le_hasSum ({0} : Finset ℕ) (fun n hn => hterm n (by simpa using hn)) hs
  have hzero : F 0 = f 0 := by simpa using hFf 0 (by simpa using hR)
  simpa only [Finset.sum_singleton, iteratedDeriv_zero, Nat.factorial_zero,
    Nat.cast_one, inv_one, pow_zero, one_smul, hzero] using hb

end D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis

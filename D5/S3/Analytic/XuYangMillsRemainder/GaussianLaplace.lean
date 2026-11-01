/- GID: D5/S3/Analytic/XuYangMillsRemainder/GaussianLaplace
   generality: G
   mirror-B: D5/B/S3/Analytic/XuYangMillsRemainder/GaussianLaplace
   mirror-E: none(waiver:kernel-checked-analytic-proof-no-external-evidence)
   anchors: [mathlib/module/Mathlib.Analysis.Convolution]
   utility: none
   digest: The exact general-parameter Gaussian kernel and its original Mills Laplace identity. -/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import D5.S3.Analytic.XuYangMillsRemainder.Result

open Set Filter Real MeasureTheory
open scoped Topology ContDiff
noncomputable section

namespace D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter

open D5.S3.Analytic.XuYangMillsRemainder.Result

/-! The general-parameter Gaussian convolution kernel, before finite subtraction. -/

def G (a t : ℝ) : ℝ :=
  t * (∫ v in (0 : ℝ)..1,
    (t ^ 2 / 4 * (1 - v ^ 2) + a) * exp (-(1 + v ^ 2) * t ^ 2 / 4)) -
      a * t * exp (-t ^ 2 / 2)

theorem gaussian_kernel_identity (a t : ℝ) :
    G a t = t ^ 3 / 4 * ∫ v in (0 : ℝ)..1,
      (1 + (2 * a - 1) * v ^ 2) * exp (-(1 + v ^ 2) * t ^ 2 / 4) := by
  have hd (v : ℝ) :
      HasDerivAt (fun v : ℝ => v * exp (-(1 + v ^ 2) * t ^ 2 / 4))
        ((1 - t ^ 2 / 2 * v ^ 2) * exp (-(1 + v ^ 2) * t ^ 2 / 4)) v := by
    convert (hasDerivAt_id v).mul
      (((((hasDerivAt_id v).pow 2).const_add 1).neg.mul_const (t ^ 2)).div_const 4).exp
      using 1 <;> (try ext w) <;> dsimp <;> ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
    (show IntervalIntegrable (fun v : ℝ =>
      (1 - t ^ 2 / 2 * v ^ 2) * exp (-(1 + v ^ 2) * t ^ 2 / 4)) volume 0 1 by
      apply Continuous.intervalIntegrable; fun_prop)
  have he' : (∫ v in (0 : ℝ)..1,
      (1 - t ^ 2 / 2 * v ^ 2) * exp (-(1 + v ^ 2) * t ^ 2 / 4)) =
      exp (-t ^ 2 / 2) := by
    simpa only [one_pow, one_mul, zero_mul, sub_zero,
      show -((1 : ℝ) + 1) * t ^ 2 / 4 = -t ^ 2 / 2 by ring] using he
  unfold G
  rw [← he', ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v _
  ring

/-! The Gaussian convolution identity for the original normalization. -/

private theorem gaussian_kernel_eq_K (t : ℝ) :
    G (-1) t = Result.K t := by
  have hd (v : ℝ) :
      HasDerivAt (fun v : ℝ => v * (1 - v ^ 2) *
        exp (-(1 + v ^ 2) * t ^ 2 / 4))
        ((1 - 3 * v ^ 2 - t ^ 2 / 2 * (v ^ 2 - v ^ 4)) *
          exp (-(1 + v ^ 2) * t ^ 2 / 4)) v := by
    convert ((hasDerivAt_id v).mul
      ((hasDerivAt_const v (1 : ℝ)).sub ((hasDerivAt_id v).pow 2))).mul
      (((((hasDerivAt_id v).pow 2).const_add 1).neg.mul_const (t ^ 2)).div_const 4).exp
      using 1 <;> (try ext w) <;> dsimp <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
    (show IntervalIntegrable (fun v : ℝ =>
      (1 - 3 * v ^ 2 - t ^ 2 / 2 * (v ^ 2 - v ^ 4)) *
        exp (-(1 + v ^ 2) * t ^ 2 / 4)) volume 0 1 by
      apply Continuous.intervalIntegrable
      fun_prop)
  have hz : (∫ v in (0 : ℝ)..1,
      (1 - 3 * v ^ 2 - t ^ 2 / 2 * (v ^ 2 - v ^ 4)) *
        exp (-(1 + v ^ 2) * t ^ 2 / 4)) = 0 := by
    have h := hi
    norm_num at h
    convert h using 1
    apply intervalIntegral.integral_congr
    intro y _
    congr 2
    ring
  have hrel : (∫ v in (0 : ℝ)..1,
      (1 - 3 * v ^ 2) * exp (-(1 + v ^ 2) * t ^ 2 / 4)) =
      t ^ 2 / 2 * (∫ v in (0 : ℝ)..1,
        v ^ 2 * (1 - v ^ 2) * exp (-(1 + v ^ 2) * t ^ 2 / 4)) := by
    calc
      _ = (∫ v in (0 : ℝ)..1,
          ((1 - 3 * v ^ 2 - t ^ 2 / 2 * (v ^ 2 - v ^ 4)) +
            t ^ 2 / 2 * (v ^ 2 * (1 - v ^ 2))) *
            exp (-(1 + v ^ 2) * t ^ 2 / 4)) := by
          apply intervalIntegral.integral_congr
          intro v _
          ring
      _ = (∫ v in (0 : ℝ)..1,
          (1 - 3 * v ^ 2 - t ^ 2 / 2 * (v ^ 2 - v ^ 4)) *
            exp (-(1 + v ^ 2) * t ^ 2 / 4) +
          t ^ 2 / 2 * (v ^ 2 * (1 - v ^ 2)) *
            exp (-(1 + v ^ 2) * t ^ 2 / 4)) := by
          apply intervalIntegral.integral_congr
          intro v _
          ring
      _ = (∫ v in (0 : ℝ)..1,
          (1 - 3 * v ^ 2 - t ^ 2 / 2 * (v ^ 2 - v ^ 4)) *
            exp (-(1 + v ^ 2) * t ^ 2 / 4)) +
          ∫ v in (0 : ℝ)..1,
            t ^ 2 / 2 * (v ^ 2 * (1 - v ^ 2)) *
              exp (-(1 + v ^ 2) * t ^ 2 / 4) := by
          rw [intervalIntegral.integral_add
            (by apply Continuous.intervalIntegrable; fun_prop)
            (by apply Continuous.intervalIntegrable; fun_prop)]
      _ = t ^ 2 / 2 * (∫ v in (0 : ℝ)..1,
          v ^ 2 * (1 - v ^ 2) * exp (-(1 + v ^ 2) * t ^ 2 / 4)) := by
          rw [hz, zero_add, ← intervalIntegral.integral_const_mul]
          congr 1
          funext v
          ring
  rw [gaussian_kernel_identity]
  unfold Result.K Result.J
  have hi : (∫ v in (0 : ℝ)..1,
      (1 + (2 * (-1 : ℝ) - 1) * v ^ 2) *
        exp (-(1 + v ^ 2) * t ^ 2 / 4)) =
      ∫ v in (0 : ℝ)..1,
        (1 - 3 * v ^ 2) * exp (-(1 + v ^ 2) * t ^ 2 / 4) := by
    apply intervalIntegral.integral_congr
    intro v _
    ring
  rw [hi, hrel]
  ring

theorem gaussian_laplace_identity (a : ℝ) {x : ℝ} (hx : 0 < x) :
    Y a (a - 2) x - (a - 1) =
      ∫ t in Ioi (0 : ℝ), exp (-x * t) * G a t := by
  let h : ℝ → ℝ := fun t => exp (-t ^ 2 / 2)
  have hh : IntegrableOn (fun t : ℝ => exp (-x * t) * h t) (Ioi 0) := by
    have he := (TwoScaleEndpointMoments.exponential_moment x hx 0).1
    simp only [← neg_mul] at he
    apply he.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp [h]
    rw [abs_of_nonneg (mul_nonneg (exp_nonneg _) (exp_nonneg _))]
    have hsq : -t ^ 2 / 2 ≤ (0 : ℝ) := by
      nlinarith [sq_nonneg t]
    have he : exp (-t ^ 2 / 2) ≤ (1 : ℝ) := exp_le_one_iff.mpr hsq
    simpa only [pow_zero, one_mul] using
      (mul_le_of_le_one_right (exp_nonneg (-x * t)) he)
  have hth : IntegrableOn (fun t : ℝ => exp (-x * t) * (t * h t)) (Ioi 0) := by
    have he := (TwoScaleEndpointMoments.exponential_moment x hx 1).1
    simp only [← neg_mul] at he
    apply he.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp [h]
    have ht0 : 0 < t := ht
    rw [abs_of_nonneg (mul_nonneg (exp_nonneg _) (mul_nonneg ht0.le (exp_nonneg _)))]
    have he : exp (-t ^ 2 / 2) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
    calc
      exp (-x * t) * (t * exp (-t ^ 2 / 2)) ≤ exp (-x * t) * t := by
        exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right ht0.le he)
          (exp_nonneg _)
      _ = t ^ 1 * exp (-x * t) := by ring
  have hr : millsRatio x = ∫ t in Ioi (0 : ℝ), exp (-x * t) * h t := by
    rw [Result.millsLaplace]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [h]
    rw [← exp_add]
    congr 1
    ring
  have hr2 : millsRatio x ^ 2 =
      ∫ t in Ioi (0 : ℝ), exp (-x * t) * Result.q0 t := by
    rw [Result.millsSquareConvolution hx.le]
    apply integral_congr_ae
    filter_upwards with t
    rw [Result.convolutionClosed]
    change exp (-x * t) * (t * (∫ v in (0 : ℝ)..1,
      exp (-(1 + v ^ 2) * t ^ 2 / 4))) =
      exp (-x * t) * Result.q0 t
    simp [Result.q0, Result.J]
  have hq0 : IntegrableOn
      (fun t : ℝ => exp (-x * t) * Result.q0 t) (Ioi 0) := by
    convert Result.JMomentIntegrable (fun _ : ℝ => 1) continuous_const 1 hx using 1
    ext t
    dsimp [Result.q0]
    ring
  have hlim : Tendsto (fun t : ℝ => exp (-x * t) * h t) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun t : ℝ => exp (-x * t)) (fun t => ?_)
      (by simpa only [rpow_zero, one_mul] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 x hx)
    dsimp [h]
    rw [abs_of_nonneg (mul_nonneg (exp_nonneg _) (exp_nonneg _))]
    exact mul_le_of_le_one_right (exp_nonneg _)
      (exp_le_one_iff.mpr (by nlinarith [sq_nonneg t]))
  have hibp := Result.laplaceIBP
    (f := h) (g := fun t => -t * h t) (x := x)
    (fun t => by
      dsimp [h]
      convert (((hasDerivAt_id t).pow 2).neg.div_const 2).exp using 1 <;>
        (try ext z) <;> dsimp <;> ring)
    hh (by
      have hthneg := hth.neg
      apply hthneg.congr
      filter_upwards with t
      dsimp
      ring) hlim
  have hth_value : (∫ t in Ioi (0 : ℝ), exp (-x * t) * (t * h t)) =
      1 - x * millsRatio x := by
    have hibp0 := hibp
    have hneg : (∫ t in Ioi (0 : ℝ), exp (-x * t) * (-t * h t)) =
        -(∫ t in Ioi (0 : ℝ), exp (-x * t) * (t * h t)) := by
      have hneg0 : (∫ t in Ioi (0 : ℝ),
          -(exp (-x * t) * (t * h t))) =
          -(∫ t in Ioi (0 : ℝ), exp (-x * t) * (t * h t)) := integral_neg _
      convert hneg0 using 1
      apply integral_congr_ae
      filter_upwards with t
      ring
    rw [hneg] at hibp0
    have hR : x * millsRatio x = x *
        (∫ t in Ioi (0 : ℝ), exp (-x * t) * h t) := congrArg (fun z : ℝ => x * z) hr
    have hibp1 := hibp0
    rw [← hR] at hibp1
    have hzero : h 0 = 1 := by simp [h]
    rw [hzero] at hibp1
    linarith
  have hGm : (∫ t in Ioi (0 : ℝ), exp (-x * t) * G (-1) t) =
      (x ^ 2 - 1) * millsRatio x ^ 2 - 3 * x * millsRatio x + 2 := by
    have hk := Result.kernelLaplace hx (millsRatio x) hr hr2
    rw [hk]
    apply integral_congr_ae
    filter_upwards with t
    exact congrArg (fun z => exp (-x * t) * z) (gaussian_kernel_eq_K t)
  have hGa : (∫ t in Ioi (0 : ℝ), exp (-x * t) * G a t) =
      (∫ t in Ioi (0 : ℝ), exp (-x * t) * G (-1) t) +
        (a + 1) * (millsRatio x ^ 2 - (∫ t in Ioi (0 : ℝ),
          exp (-x * t) * (t * h t))) := by
    have hdiff : ∀ t : ℝ, G a t = G (-1) t + (a + 1) *
        (Result.q0 t - t * h t) := by
      intro t
      have haff (c : ℝ) :
          (∫ v in (0 : ℝ)..1,
            (t ^ 2 / 4 * (1 - v ^ 2) + c) *
              exp (-(1 + v ^ 2) * t ^ 2 / 4)) =
            (∫ v in (0 : ℝ)..1,
              t ^ 2 / 4 * (1 - v ^ 2) *
                exp (-(1 + v ^ 2) * t ^ 2 / 4)) +
              c * (∫ v in (0 : ℝ)..1,
                exp (-(1 + v ^ 2) * t ^ 2 / 4)) := by
        calc
          _ = (∫ v in (0 : ℝ)..1,
              t ^ 2 / 4 * (1 - v ^ 2) *
                  exp (-(1 + v ^ 2) * t ^ 2 / 4) +
                c * exp (-(1 + v ^ 2) * t ^ 2 / 4)) := by
              apply intervalIntegral.integral_congr
              intro v _
              ring
          _ = _ := by
            rw [intervalIntegral.integral_add
              (by apply Continuous.intervalIntegrable; fun_prop)
              (by apply Continuous.intervalIntegrable; fun_prop),
              ← intervalIntegral.integral_const_mul]
      unfold G Result.q0 Result.J
      rw [haff a, haff (-1)]
      dsimp [h]
      congr 1
      ring
    have hsplit : (∫ t in Ioi (0 : ℝ), exp (-x * t) * G a t) =
        (∫ t in Ioi (0 : ℝ), exp (-x * t) *
          (G (-1) t + (a + 1) * (Result.q0 t - t * h t))) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hdiff]
    have hsecond : IntegrableOn (fun t : ℝ => exp (-x * t) *
        ((a + 1) * (Result.q0 t - t * h t))) (Ioi 0) := by
      have hc := (hq0.sub hth).const_mul (a + 1)
      apply hc.congr
      filter_upwards with t
      dsimp
      ring
    calc
      _ = (∫ t in Ioi (0 : ℝ), exp (-x * t) * G (-1) t) +
          (∫ t in Ioi (0 : ℝ), exp (-x * t) *
            ((a + 1) * (Result.q0 t - t * h t))) := by
        rw [hsplit]
        calc
          _ = ∫ t in Ioi (0 : ℝ),
              (exp (-x * t) * G (-1) t) +
                (exp (-x * t) * ((a + 1) * (Result.q0 t - t * h t))) := by
                apply integral_congr_ae
                filter_upwards with t
                ring
          _ = _ := integral_add (by
            have hi := (Result.JMomentIntegrable (fun v => v ^ 2 * (1 - v ^ 2))
              (by fun_prop) 5 hx).div_const 8
            apply hi.congr
            filter_upwards with t
            rw [gaussian_kernel_eq_K]
            dsimp [Result.K]
            ring) hsecond
      _ = _ := by
        have hconst : (∫ t in Ioi (0 : ℝ), exp (-x * t) *
            ((a + 1) * (Result.q0 t - t * h t))) =
            (a + 1) * (∫ t in Ioi (0 : ℝ), exp (-x * t) *
              (Result.q0 t - t * h t)) := by
          calc
            _ = ∫ t in Ioi (0 : ℝ), (a + 1) *
                (exp (-x * t) * (Result.q0 t - t * h t)) := by
                  apply integral_congr_ae
                  filter_upwards with t
                  ring
            _ = _ := integral_const_mul _ _
        rw [hconst]
        have hsub : (∫ t in Ioi (0 : ℝ), exp (-x * t) *
            (Result.q0 t - t * h t)) =
            (∫ t in Ioi (0 : ℝ), exp (-x * t) * Result.q0 t) -
              ∫ t in Ioi (0 : ℝ), exp (-x * t) * (t * h t) := by
          rw [← integral_sub hq0 hth]
          apply integral_congr_ae
          filter_upwards with t
          ring
        rw [hsub, hr2]
  rw [hGa, hth_value, hGm]
  unfold Y
  rw [hr]
  ring

end D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter

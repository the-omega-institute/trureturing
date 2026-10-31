/- GID: D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter
   generality: G
   mirror-B: D5/B/S3/Analytic/XuYangMillsRemainder/GeneralParameter
   mirror-E: none
   anchors: [D5/S3/Analytic/XuYangMillsRemainder/GeneralParameterFoundation]
   utility: none
   digest: Complete original Mills sign and complete-monotonicity classification. -/

module

public import D5.S3.Analytic.XuYangMillsRemainder.GeneralParameterFoundation
import all D5.S3.Analytic.XuYangMillsRemainder.GeneralParameterFoundation

/-! Exact Laplace analysis, ordinary derivatives and both sharp classification chains. -/

open Set Filter Real MeasureTheory
open scoped Topology ContDiff
noncomputable section

namespace D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter

open D5.S3.Analytic.XuYangMillsRemainder.Result

/-! Absolute Laplace control and exact finite subtraction for every real parameter. -/

private theorem kernel_continuous (r : ℕ) (a : ℝ) : Continuous (L r a) := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      ((1 - 2 * a) * p.2 ^ 2 - 1) * E r (p.1 ^ 2 / 4 * (1 + p.2 ^ 2))) :=
    (by fun_prop : Continuous (fun p : ℝ × ℝ => (1 - 2 * a) * p.2 ^ 2 - 1)).mul
      ((e_continuous r).comp (by fun_prop))
  have hi := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun t v : ℝ => ((1 - 2 * a) * v ^ 2 - 1) *
      E r (t ^ 2 / 4 * (1 + v ^ 2))) hc (s := Icc (0 : ℝ) 1) isCompact_Icc
  simp_rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
  exact (by fun_prop : Continuous (fun t : ℝ => t ^ 3 / 4)).mul hi

private theorem kernel_polynomial_bound (r : ℕ) (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖L r a t‖ ≤ (|1 - 2 * a| + 1) * t ^ (2 * r + 5) := by
  have hb (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      ‖((1 - 2 * a) * v ^ 2 - 1) * E r (t ^ 2 / 4 * (1 + v ^ 2))‖ ≤
        (|1 - 2 * a| + 1) * t ^ (2 * (r + 1)) := by
    have hv2 : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
    have hy : 0 ≤ t ^ 2 / 4 * (1 + v ^ 2) := by positivity
    have hyt : t ^ 2 / 4 * (1 + v ^ 2) ≤ t ^ 2 := by nlinarith [sq_nonneg t]
    have he := expRemainderBounds (r + 1) hy
    rw [← e_original] at he
    have he' : E r (t ^ 2 / 4 * (1 + v ^ 2)) ≤ t ^ (2 * (r + 1)) := by
      calc
        _ ≤ (t ^ 2 / 4 * (1 + v ^ 2)) ^ (r + 1) / (r + 1).factorial := he.2
        _ ≤ (t ^ 2) ^ (r + 1) :=
          (div_le_self (by positivity)
            (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (r + 1)))).trans
              (pow_le_pow_left₀ hy hyt _)
        _ = _ := by rw [← pow_mul]
    have hw : ‖(1 - 2 * a) * v ^ 2 - 1‖ ≤ |1 - 2 * a| + 1 := by
      calc
        _ ≤ ‖(1 - 2 * a) * v ^ 2‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
        _ ≤ _ := by
          rw [norm_mul, Real.norm_of_nonneg (sq_nonneg v), norm_one, Real.norm_eq_abs]
          nlinarith [mul_le_of_le_one_right (abs_nonneg (1 - 2 * a)) hv2]
    rw [norm_mul, Real.norm_of_nonneg he.1]
    exact mul_le_mul hw he' he.1 (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := (|1 - 2 * a| + 1) * t ^ (2 * (r + 1)))
    (fun v hv => hb v (Ioc_subset_Icc_self
      (by simpa only [uIoc_of_le zero_le_one] using hv)))
  simp only [sub_zero, abs_one, mul_one] at hi
  unfold L
  rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ t ^ 3 / 4)]
  calc
    _ ≤ t ^ 3 / 4 * ((|1 - 2 * a| + 1) * t ^ (2 * (r + 1))) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ (|1 - 2 * a| + 1) * t ^ (2 * r + 5) := by
      rw [show 2 * r + 5 = 3 + 2 * (r + 1) by omega, pow_add]
      nlinarith [mul_nonneg (pow_nonneg ht 3)
        (mul_nonneg (by positivity : 0 ≤ |1 - 2 * a| + 1)
          (pow_nonneg ht (2 * (r + 1))))]

private theorem kernel_exponential_moments (r m : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t ^ m * exp (-x * t) * L r a t) (Ioi 0) := by
  have he := (TwoScaleEndpointMoments.exponential_moment x hx (m + 2 * r + 5)).1
  simp only [← neg_mul] at he
  apply (he.const_mul (|1 - 2 * a| + 1)).mono'
    (((by fun_prop : Continuous (fun t : ℝ => t ^ m * exp (-x * t))).mul
      (kernel_continuous r a)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖t ^ m * exp (-x * t) * L r a t‖ ≤ _
  rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _))]
  calc
    _ ≤ t ^ m * exp (-x * t) * ((|1 - 2 * a| + 1) * t ^ (2 * r + 5)) :=
      mul_le_mul_of_nonneg_left (kernel_polynomial_bound r a ht.le)
        (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _))
    _ = _ := by
      rw [show m + 2 * r + 5 = m + (2 * r + 5) by omega, pow_add]
      ring

private theorem kernel_rec (r : ℕ) (a t : ℝ) :
    L (r + 1) a t =
      -(t ^ (2 * r + 5) / ((4 : ℝ) ^ (r + 2) * (r + 1).factorial) *
        (I (r + 1) + (2 * a - 1) * B (r + 1))) - L r a t := by
  have he (y : ℝ) : E (r + 1) y = y ^ (r + 1) / (r + 1).factorial - E r y := by
    simpa only [e_original] using expRemainderRec (r + 1) y
  have hc : Continuous (fun v : ℝ => ((1 - 2 * a) * v ^ 2 - 1) *
      E r (t ^ 2 / 4 * (1 + v ^ 2))) :=
    (by fun_prop : Continuous (fun v : ℝ => (1 - 2 * a) * v ^ 2 - 1)).mul
      ((e_continuous r).comp (by fun_prop))
  have hid (v : ℝ) : ((1 - 2 * a) * v ^ 2 - 1) *
      E (r + 1) (t ^ 2 / 4 * (1 + v ^ 2)) =
      -(t ^ (2 * (r + 1)) / ((4 : ℝ) ^ (r + 1) * (r + 1).factorial)) *
        ((1 + v ^ 2) ^ (r + 1) + (2 * a - 1) * (v ^ 2 * (1 + v ^ 2) ^ (r + 1))) -
      ((1 - 2 * a) * v ^ 2 - 1) * E r (t ^ 2 / 4 * (1 + v ^ 2)) := by
    rw [he, mul_pow, div_pow, ← pow_mul]
    ring
  unfold L
  simp_rw [hid]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (hc.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul]
  change t ^ 3 / 4 * (_ * (I (r + 1) + (2 * a - 1) * B (r + 1)) - _) = _
  rw [show 2 * r + 5 = 3 + 2 * (r + 1) by omega, pow_add,
    show r + 2 = (r + 1) + 1 by omega, pow_succ (4 : ℝ)]
  ring

private theorem kernel_laplace_rec (r : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), exp (-x * t) * L (r + 1) a t) =
      -u (r + 3) a (a - 2) / x ^ (2 * r + 6) -
        ∫ t in Ioi (0 : ℝ), exp (-x * t) * L r a t := by
  have hk : IntegrableOn (fun t : ℝ => exp (-x * t) * L r a t) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using kernel_exponential_moments r 0 a hx
  have hm := TwoScaleEndpointMoments.exponential_moment x hx (2 * r + 5)
  simp only [← neg_mul] at hm
  let c := -(I (r + 1) + (2 * a - 1) * B (r + 1)) /
    ((4 : ℝ) ^ (r + 2) * (r + 1).factorial)
  calc
    _ = ∫ t in Ioi (0 : ℝ), (t ^ (2 * r + 5) * exp (-x * t)) * c -
        exp (-x * t) * L r a t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [kernel_rec]
      dsimp [c]
      ring
    _ = (∫ t in Ioi (0 : ℝ), t ^ (2 * r + 5) * exp (-x * t)) * c -
        ∫ t in Ioi (0 : ℝ), exp (-x * t) * L r a t := by
      rw [integral_sub (hm.1.mul_const c) hk, integral_mul_const]
    _ = _ := by
      rw [hm.2, show r + 3 = (r + 1) + 2 by omega, coefficient_identity]
      dsimp [c]
      simp only [show 2 * (r + 1) + 3 = 2 * r + 5 by omega,
        show 2 * r + 5 + 1 = 2 * r + 6 by omega,
        show r + 1 + 1 = r + 2 by omega]
      ring

private theorem kernel_zero (a t : ℝ) :
    L 0 a t = G a t - t ^ 3 / 4 * (I 0 + (2 * a - 1) * B 0) := by
  have he (y : ℝ) : E 0 y = 1 - exp (-y) := by
    rw [e_original, expRemainder_eq]
    norm_num
  rw [gaussian_kernel_identity]
  unfold L
  simp_rw [he]
  have hi : (∫ v in (0 : ℝ)..1, ((1 - 2 * a) * v ^ 2 - 1) *
      (1 - exp (-(t ^ 2 / 4 * (1 + v ^ 2)))) ) =
      (∫ v in (0 : ℝ)..1, (1 + (2 * a - 1) * v ^ 2) *
        exp (-(1 + v ^ 2) * t ^ 2 / 4)) - (I 0 + (2 * a - 1) * B 0) := by
    rw [show I 0 + (2 * a - 1) * B 0 =
        ∫ v in (0 : ℝ)..1, 1 + (2 * a - 1) * v ^ 2 by
      simp only [I, B, pow_zero, mul_one]
      rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul]]
    rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [show -(t ^ 2 / 4 * (1 + v ^ 2)) = -(1 + v ^ 2) * t ^ 2 / 4 by ring]
    ring
  rw [hi]
  ring

private theorem gaussian_exponential_integrable (a : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => exp (-x * t) * G a t) (Ioi 0) := by
  have hk : IntegrableOn (fun t : ℝ => exp (-x * t) * L 0 a t) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using kernel_exponential_moments 0 0 a hx
  have hm := (TwoScaleEndpointMoments.exponential_moment x hx 3).1
  simp only [← neg_mul] at hm
  apply (hk.add (hm.mul_const ((I 0 + (2 * a - 1) * B 0) / 4))).congr
  filter_upwards with t
  dsimp only [Pi.add_apply]
  rw [kernel_zero]
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

private theorem gaussian_laplace_identity (a : ℝ) {x : ℝ} (hx : 0 < x) :
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
          _ = _ := integral_add (gaussian_exponential_integrable (-1) hx) hsecond
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

private theorem kernel_laplace_zero (a : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), exp (-x * t) * L 0 a t) =
      (∫ t in Ioi (0 : ℝ), exp (-x * t) * G a t) - u 2 a (a - 2) / x ^ 4 := by
  have hm := TwoScaleEndpointMoments.exponential_moment x hx 3
  simp only [← neg_mul] at hm
  calc
    _ = ∫ t in Ioi (0 : ℝ), exp (-x * t) * G a t -
        (t ^ 3 * exp (-x * t)) * ((I 0 + (2 * a - 1) * B 0) / 4) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [kernel_zero]
      ring
    _ = _ := by
      rw [integral_sub (gaussian_exponential_integrable a hx) (hm.1.mul_const _),
        integral_mul_const, hm.2]
      have hu := coefficient_identity 0 a
      norm_num at hu
      rw [hu]
      ring

private theorem laplace_finite_subtraction (r : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), exp (-x * t) * L r a t) =
      (-1 : ℝ) ^ (r + 2) *
        ((∫ t in Ioi (0 : ℝ), exp (-x * t) * G a t) -
          ∑ k ∈ Finset.Icc 1 (r + 2), (-1 : ℝ) ^ k * u k a (a - 2) / x ^ (2 * k)) := by
  induction r with
  | zero =>
    simpa [show Finset.Icc 1 2 = {1, 2} by decide, coefficient_one_zero]
      using kernel_laplace_zero a hx
  | succ r ih =>
    rw [kernel_laplace_rec r a hx, ih,
      show r + 1 + 2 = (r + 2) + 1 by omega,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ (r + 2) + 1), pow_succ]
    have hs : (-1 : ℝ) ^ (r + 2) * (-1 : ℝ) ^ (r + 2) = 1 := by
      rw [← mul_pow]
      norm_num
    have hp : 2 * (r + 2 + 1) = 2 * r + 6 := by omega
    simp only [pow_succ, hp]
    linear_combination (u (r + 3) a (a - 2) / x ^ (2 * r + 6)) * hs

private theorem f_laplace_defect (r : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    F (r + 2) a x - (∫ t in Ioi (0 : ℝ), exp (-x * t) * L r a t) =
      (-1 : ℝ) ^ (r + 2) *
        (Y a (a - 2) x - (a - 1) - ∫ t in Ioi (0 : ℝ), exp (-x * t) * G a t) := by
  rw [laplace_finite_subtraction r a hx]
  unfold F D
  ring

/-! Differentiation of the actual signed kernel requires no parameter sign premise. -/

private theorem signed_kernel_moment_deriv (r m : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (moment (L r a) m) (moment (L r a) (m + 1) x) x := by
  have hint : IntegrableOn (fun t : ℝ => (-t) ^ m * exp (-x * t) * L r a t) (Ioi 0) := by
    apply ((kernel_exponential_moments r m a hx).const_mul ((-1 : ℝ) ^ m)).congr
    filter_upwards with t
    rw [neg_eq_neg_one_mul, mul_pow]
    ring
  have hb := (TwoScaleEndpointMoments.exponential_moment (x / 2) (half_pos hx)
    (m + 1 + 2 * r + 5)).1.const_mul (|1 - 2 * a| + 1)
  simp only [← neg_mul] at hb
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun y t : ℝ => (-t) ^ m * exp (-y * t) * L r a t)
    (F' := fun y t : ℝ => (-t) ^ (m + 1) * exp (-y * t) * L r a t)
    (s := Ioi (x / 2))
    (bound := fun t : ℝ => (|1 - 2 * a| + 1) *
      (t ^ (m + 1 + 2 * r + 5) * exp (-(x / 2) * t)))
    (Ioi_mem_nhds (by linarith : x / 2 < x))
    (Eventually.of_forall (fun y =>
      (((by fun_prop : Continuous (fun t : ℝ => (-t) ^ m * exp (-y * t))).mul
        (kernel_continuous r a)).aestronglyMeasurable))) hint
    (((by fun_prop : Continuous (fun t : ℝ => (-t) ^ (m + 1) * exp (-x * t))).mul
      (kernel_continuous r a)).aestronglyMeasurable)
    ?_ hb ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro y hy
    have hex : exp (-y * t) ≤ exp (-(x / 2) * t) := by
      apply exp_le_exp.mpr
      change x / 2 < y at hy
      change 0 < t at ht
      nlinarith
    simp only [norm_mul, norm_pow, norm_neg, Real.norm_of_nonneg ht.le,
      Real.norm_of_nonneg (exp_nonneg _)]
    calc
      _ ≤ t ^ (m + 1) * exp (-(x / 2) * t) * ‖L r a t‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hex (pow_nonneg ht.le _)) (norm_nonneg _)
      _ ≤ t ^ (m + 1) * exp (-(x / 2) * t) *
          ((|1 - 2 * a| + 1) * t ^ (2 * r + 5)) :=
        mul_le_mul_of_nonneg_left (kernel_polynomial_bound r a ht.le)
          (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _))
      _ = _ := by
        rw [show m + 1 + 2 * r + 5 = (m + 1) + (2 * r + 5) by omega, pow_add]
        ring
  · filter_upwards with t
    intro y _
    convert ((((hasDerivAt_id y).neg.mul_const t).exp).const_mul
      ((-t) ^ m)).mul_const (L r a t) using 1 <;>
      simp only [Pi.neg_apply, id_eq, pow_succ] <;> ring

private theorem signed_kernel_moment_iterated (r : ℕ) (a : ℝ) (m : ℕ) :
    EqOn (iteratedDeriv m (moment (L r a) 0)) (moment (L r a) m) (Ioi 0) := by
  induction m with
  | zero => intro x _; rfl
  | succ m ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv m (moment (L r a) 0) =ᶠ[𝓝 x] moment (L r a) m := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact ih hy
    exact he.deriv_eq.trans (signed_kernel_moment_deriv r m a hx).deriv

/-! The Gaussian identity removes the defect and leaves the actual original F. -/

private theorem actual_f_laplace (r : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    F (r + 2) a x = ∫ t in Ioi (0 : ℝ), exp (-x * t) * L r a t := by
  have h := f_laplace_defect r a hx
  rw [gaussian_laplace_identity a hx] at h
  linarith

private theorem actual_f_iterated_deriv (r m : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv m (F (r + 2) a) x =
      ∫ t in Ioi (0 : ℝ), (-t) ^ m * exp (-x * t) * L r a t := by
  have he : EqOn (F (r + 2) a) (moment (L r a) 0) (Ioi 0) := by
    intro y hy
    simpa only [moment, pow_zero, one_mul] using actual_f_laplace r a hy
  have hd := he.iteratedDeriv_of_isOpen isOpen_Ioi m hx
  rw [signed_kernel_moment_iterated r a m hx] at hd
  exact hd

private theorem positive_cm_sufficiency (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (ha : a ≤ theta (n - 2)) : completelyMonotone n a := by
  let r : ℕ := n - 2
  have hnr : n = r + 2 := by
    dsimp [r]
    omega
  have ha' : a ≤ theta r := by
    simpa [r] using ha
  rw [hnr]
  refine ⟨(regularity_and_origin (r + 2) (by omega) a).1, ?_⟩
  intro m x hx
  rw [actual_f_iterated_deriv r m a hx, ← integral_const_mul]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hs : (-1 : ℝ) ^ m * (-t) ^ m = t ^ m := by
    rw [← mul_pow]
    congr 1
    ring
  rw [← mul_assoc, ← mul_assoc, hs]
  exact mul_nonneg
    (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _))
    ((kernel_closed_ranges r a ht).1 ha').le

private theorem negative_cm_sufficiency (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (ha : theta (n - 1) ≤ a) :
    CompletelyMonotoneOn (fun x => -F n a x) := by
  let r : ℕ := n - 2
  have hnr : n = r + 2 := by
    dsimp [r]
    omega
  have hna : n - 1 = r + 1 := by
    dsimp [r]
    omega
  have ha' : theta (r + 1) ≤ a := by
    rw [← hna]
    exact ha
  rw [hnr]
  refine ⟨(regularity_and_origin (r + 2) (by omega) a).1.neg, ?_⟩
  intro m x hx
  have hfun : (fun x : ℝ => -F (r + 2) a x) = -(F (r + 2) a) := by
    rfl
  rw [hfun, iteratedDeriv_neg, actual_f_iterated_deriv r m a hx]
  rw [← integral_neg, ← integral_const_mul]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hs : (-1 : ℝ) ^ m * (-(-t) ^ m) = -t ^ m := by
    calc
      (-1 : ℝ) ^ m * (-(-t) ^ m) = -(((-1 : ℝ) ^ m) * (-t) ^ m) := by ring
      _ = -t ^ m := by
        rw [← mul_pow]
        norm_num
  calc
    0 ≤ ((-t ^ m) * exp (-x * t)) * L r a t := by
      have htm : -t ^ m ≤ 0 := neg_nonpos.mpr (pow_nonneg ht0.le _)
      have hfirst : (-t ^ m) * exp (-x * t) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg htm (exp_nonneg _)
      exact mul_nonneg_of_nonpos_of_nonpos hfirst
        ((kernel_closed_ranges r a ht0).2 ha').le
    _ = (-1 : ℝ) ^ m * (-((-t) ^ m * exp (-x * t) * L r a t)) := by
      rw [← hs]
      ring

private theorem positive_chain (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    (globalNonnegative n a ↔ completelyMonotone n a) ∧
      (completelyMonotone n a ↔ a ≤ theta (n - 2)) := by
  constructor
  · constructor
    · intro h
      exact positive_cm_sufficiency n hn a (positive_sign_necessary n hn a h)
    · exact cm_sign_projections n a
  · constructor
    · exact positive_cm_necessary n hn a
    · exact positive_cm_sufficiency n hn a

/-! A quantitative next-remainder bound gives the original infinity limit. -/

private theorem actual_f_bound (r : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖F (r + 2) a x‖ ≤
      (|1 - 2 * a| + 1) * (2 * r + 5).factorial / x ^ (2 * r + 6) := by
  have hm := TwoScaleEndpointMoments.exponential_moment x hx (2 * r + 5)
  simp only [← neg_mul] at hm
  rw [actual_f_laplace r a hx]
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ),
        (|1 - 2 * a| + 1) * (t ^ (2 * r + 5) * exp (-x * t)) := by
      apply norm_integral_le_of_norm_le (hm.1.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, Real.norm_of_nonneg (exp_nonneg _)]
      calc
        _ ≤ exp (-x * t) * ((|1 - 2 * a| + 1) * t ^ (2 * r + 5)) :=
          mul_le_mul_of_nonneg_left (kernel_polynomial_bound r a ht.le) (exp_nonneg _)
        _ = _ := by ring
    _ = _ := by
      rw [integral_const_mul, hm.2]
      simp only [show 2 * r + 5 + 1 = 2 * r + 6 by omega]
      ring

private theorem rescaled_f_vanishes_at_infinity (r : ℕ) (a : ℝ) :
    Tendsto (fun x : ℝ => x ^ (2 * r + 4) * F (r + 2) a x) atTop (𝓝 0) := by
  have hb : ∀ᶠ x : ℝ in atTop,
      ‖x ^ (2 * r + 4) * F (r + 2) a x‖ ≤
        ((|1 - 2 * a| + 1) * (2 * r + 5).factorial) * (x⁻¹) ^ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hx.le _)]
    calc
      _ ≤ x ^ (2 * r + 4) *
          ((|1 - 2 * a| + 1) * (2 * r + 5).factorial / x ^ (2 * r + 6)) :=
        mul_le_mul_of_nonneg_left (actual_f_bound r a hx) (pow_nonneg hx.le _)
      _ = _ := by
        rw [show 2 * r + 6 = (2 * r + 4) + 2 by omega, pow_add]
        field_simp
        simp only [pow_add]
        ring
  apply squeeze_zero_norm' hb
  simpa using (tendsto_const_nhds (x :=
    (|1 - 2 * a| + 1) * ((2 * r + 5).factorial : ℝ))).mul
      ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).pow 2)

private theorem infinity_endpoint (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    Tendsto (fun x : ℝ => x ^ (2 * n + 2) * F n a x) atTop
      (𝓝 (-u (n + 1) a (a - 2))) := by
  let r := n - 2
  have hnr : n = r + 2 := by dsimp [r]; omega
  rw [hnr]
  have hl := (tendsto_const_nhds (x := -u (r + 3) a (a - 2))).sub
    (rescaled_f_vanishes_at_infinity (r + 1) a)
  simp only [sub_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hr := kernel_laplace_rec r a hx
  rw [← actual_f_laplace (r + 1) a hx, ← actual_f_laplace r a hx] at hr
  have hp : x ^ (2 * r + 6) ≠ 0 := pow_ne_zero _ hx.ne'
  have he : x ^ (2 * r + 6) * F (r + 2) a x =
      -u (r + 3) a (a - 2) - x ^ (2 * r + 6) * F (r + 3) a x := by
    have hh := (eq_div_iff hp).mp (show F (r + 2) a x + F (r + 3) a x =
        -u (r + 3) a (a - 2) / x ^ (2 * r + 6) by
      simpa only [show r + 1 + 2 = r + 3 by omega] using (by linarith :
        F (r + 2) a x + F (r + 1 + 2) a x =
          -u (r + 3) a (a - 2) / x ^ (2 * r + 6)))
    nlinarith [hh]
  simpa only [show 2 * (r + 2) + 2 = 2 * r + 6 by omega,
    show 2 * (r + 1) + 4 = 2 * r + 6 by omega,
    show r + 1 + 2 = r + 3 by omega, show r + 2 + 1 = r + 3 by omega] using he.symm

private theorem negative_sign_sharp_necessary (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (h : globalNonpositive n a) : theta (n - 1) ≤ a := by
  have hl := (infinity_endpoint n hn a).neg
  have hev : ∀ᶠ x : ℝ in atTop, -(x ^ (2 * n + 2) * F n a x) ∈ Ici (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    change 0 ≤ -(x ^ (2 * n + 2) * F n a x)
    rw [neg_mul_eq_mul_neg]
    exact mul_nonneg (pow_nonneg hx.le _) (h x hx)
  have hu : 0 ≤ u (n + 1) a (a - 2) := by
    simpa only [neg_neg, mem_Ici] using isClosed_Ici.mem_of_tendsto hl hev
  have hs := (coefficient_threshold_signs (n - 1) a).2
  rw [show n - 1 + 2 = n + 1 by omega] at hs
  exact hs.mp hu

private theorem negative_chain (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    (globalNonpositive n a ↔ CompletelyMonotoneOn (fun x => -F n a x)) ∧
      (CompletelyMonotoneOn (fun x => -F n a x) ↔ theta (n - 1) ≤ a) := by
  constructor
  · exact ⟨fun h => negative_cm_sufficiency n hn a
      (negative_sign_sharp_necessary n hn a h), neg_cm_sign_projection n a⟩
  · exact ⟨fun h => negative_sign_sharp_necessary n hn a
      (neg_cm_sign_projection n a h), negative_cm_sufficiency n hn a⟩

public theorem result : theorem21 := by
  intro n hn a
  exact ⟨positive_chain n hn a, negative_chain n hn a⟩

end D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter

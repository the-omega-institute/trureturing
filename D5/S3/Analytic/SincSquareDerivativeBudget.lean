/- GID: D5/S3/Analytic/SincSquareDerivativeBudget
   generality: G
   mirror-B: D5/B/S3/Analytic/SincSquareDerivativeBudget
   mirror-E: none(waiver:unbounded-symbolic-derivative-estimate)
   anchors: []
   utility: none
   digest: Positive integral recurrences bound all derivatives of the entire cosine root. -/

import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open MeasureTheory Set Filter
open scoped Topology Nat

namespace SincSquareDerivativeBudget

/-- The entire extension of `cos (sqrt t)`, defined by its everywhere convergent series. -/
noncomputable def psi : ℝ → ℝ :=
  FormalMultilinearSeries.ofScalarsSum (fun k => (-1 : ℝ) ^ k / (2 * k)!)

private theorem psi_radius :
    (FormalMultilinearSeries.ofScalars ℝ (fun k => (-1 : ℝ) ^ k / (2 * k)!)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  convert (Real.hasSum_cosh (Real.sqrt r)).summable using 1
  ext k
  rw [FormalMultilinearSeries.ofScalars_norm]
  simp only [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_natCast,
    one_div, mul_comm _ ((r : ℝ) ^ k)]
  rw [show 2 * k = 2 * k from rfl, pow_mul, Real.sq_sqrt r.coe_nonneg]
  rfl

private theorem psi_smooth : ContDiff ℝ ⊤ psi := by
  apply AnalyticOnNhd.contDiff
  intro t _
  apply (FormalMultilinearSeries.analyticOnNhd _)
  simp [psi_radius, Metric.eball_top]

private theorem psi_eq_cos {t : ℝ} (ht : 0 ≤ t) : psi t = Real.cos (Real.sqrt t) := by
  rw [psi, FormalMultilinearSeries.ofScalars_sum_eq, Real.cos_eq_tsum]
  apply tsum_congr
  intro k
  simp only [smul_eq_mul, pow_mul, Real.sq_sqrt ht]
  ring

private theorem psi_zero : psi 0 = 1 := by
  simp [psi, FormalMultilinearSeries.ofScalarsSum_zero]

private theorem psi_hasDerivAt_pos {t : ℝ} (ht : 0 < t) :
    HasDerivAt psi (-Real.sin (Real.sqrt t) / (2 * Real.sqrt t)) t := by
  have heq : psi =ᶠ[𝓝 t] (fun s => Real.cos (Real.sqrt s)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact psi_eq_cos hs.le
  simpa only [div_eq_mul_inv, neg_mul, one_mul] using
    ((Real.hasDerivAt_sqrt ht.ne').cos).congr_of_eventuallyEq heq

private theorem psi_deriv_integral_pos {t : ℝ} (ht : 0 < t) :
    deriv psi t = -(1 / 2 : ℝ) * ∫ r in (0 : ℝ)..1, psi (r ^ 2 * t) := by
  have hi : (∫ r in (0 : ℝ)..1, psi (r ^ 2 * t)) =
      Real.sin (Real.sqrt t) / Real.sqrt t := by
    calc
      _ = ∫ r in (0 : ℝ)..1, Real.cos (r * Real.sqrt t) := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
        dsimp only
        rw [psi_eq_cos (mul_nonneg (sq_nonneg _) ht.le),
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr.1]
      _ = _ := by
        rw [intervalIntegral.integral_comp_mul_right _ (Real.sqrt_ne_zero'.mpr ht),
          integral_cos]
        simp [div_eq_mul_inv, mul_comm]
  rw [(psi_hasDerivAt_pos ht).deriv, hi]
  ring

/-- Differentiate a continuous parameter integral with continuous partial derivative. -/
private theorem integral_hasDerivAt {F F' : ℝ → ℝ → ℝ}
    (hF : Continuous F.uncurry) (hF' : Continuous F'.uncurry)
    (hd : ∀ x r, HasDerivAt (fun y => F y r) (F' x r) x) (x : ℝ) :
    HasDerivAt (fun y => ∫ r in (0 : ℝ)..1, F y r)
      (∫ r in (0 : ℝ)..1, F' x r) x := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (x - 1) (x + 1) ×ˢ Icc (0 : ℝ) 1) hF'.continuousOn
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo (x - 1) (x + 1)) (bound := fun _ => C)
    (Ioo_mem_nhds (by linarith) (by linarith)) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_).2
  · exact Filter.Eventually.of_forall fun y => (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro r hr y hy
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
    exact hC (y, r) ⟨⟨hy.1.le, hy.2.le⟩, ⟨hr.1.le, hr.2⟩⟩
  · exact Filter.Eventually.of_forall fun r _ y _ => hd y r


private theorem weighted_integral_iteratedDeriv (w a : ℝ → ℝ)
    (hw : Continuous w) (ha : Continuous a) (n : ℕ) :
    iteratedDeriv n (fun t => ∫ r in (0 : ℝ)..1, w r * psi (a r * t)) =
      fun t => ∫ r in (0 : ℝ)..1, w r * (a r) ^ n * iteratedDeriv n psi (a r * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hc := psi_smooth.continuous_iteratedDeriv n (by simp)
    have hc' := psi_smooth.continuous_iteratedDeriv (n + 1) (by simp)
    apply HasDerivAt.deriv
    apply integral_hasDerivAt
      (F := fun x r => w r * (a r) ^ n * iteratedDeriv n psi (a r * x))
      (F' := fun x r => w r * (a r) ^ (n + 1) * iteratedDeriv (n + 1) psi (a r * x))
    · exact ((hw.comp continuous_snd).mul ((ha.comp continuous_snd).pow _)).mul
        (hc.comp ((ha.comp continuous_snd).mul continuous_fst))
    · exact ((hw.comp continuous_snd).mul ((ha.comp continuous_snd).pow _)).mul
        (hc'.comp ((ha.comp continuous_snd).mul continuous_fst))
    · intro x r
      have hd := ((psi_smooth.differentiable_iteratedDeriv n (by simp) (a r * x)).hasDerivAt.comp x
        ((hasDerivAt_id x).const_mul (a r))).const_mul (w r * (a r) ^ n)
      simp only [iteratedDeriv_succ, pow_succ] at hd ⊢
      convert! hd using 1 <;> ring

private theorem integral_iteratedDeriv (n : ℕ) :
    iteratedDeriv n (fun t => ∫ r in (0 : ℝ)..1, psi (r ^ 2 * t)) =
      fun t => ∫ r in (0 : ℝ)..1, r ^ (2 * n) * iteratedDeriv n psi (r ^ 2 * t) := by
  have h := weighted_integral_iteratedDeriv (fun _ => 1) (fun r => r ^ 2)
    continuous_const (continuous_id.pow 2) n
  simpa only [one_mul, pow_mul] using h

/-- A positive-kernel recurrence retaining cancellation at every derivative order. -/
theorem psi_derivative_integral (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDeriv (n + 1) psi t =
      -(1 / 2 : ℝ) * ∫ r in (0 : ℝ)..1, r ^ (2 * n) * iteratedDeriv n psi (r ^ 2 * t) := by
  have heq : EqOn (iteratedDeriv (n + 1) psi)
      (fun t => -(1 / 2 : ℝ) * ∫ r in (0 : ℝ)..1,
        r ^ (2 * n) * iteratedDeriv n psi (r ^ 2 * t)) (Ioi 0) := by
    intro t ht
    have he : deriv psi =ᶠ[𝓝 t] (fun s => -(1 / 2 : ℝ) * ∫ r in (0 : ℝ)..1, psi (r ^ 2 * s)) := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      exact psi_deriv_integral_pos hs
    rw [iteratedDeriv_succ', he.iteratedDeriv_eq n, iteratedDeriv_const_mul_field,
      integral_iteratedDeriv]
  have hc := psi_smooth.continuous_iteratedDeriv n (by simp)
  have hc' := psi_smooth.continuous_iteratedDeriv (n + 1) (by simp)
  apply heq.closure hc' ?_ (by simpa using ht)
  apply Continuous.const_mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (continuous_snd.pow _).mul (hc.comp ((continuous_snd.pow 2).mul continuous_fst))

/-- The cosine square-root extension has a factorial derivative budget on the whole half-line. -/
theorem psi_derivative_bound (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |iteratedDeriv n psi t| ≤ (n ! : ℝ) / (2 * n)! := by
  induction n generalizing t with
  | zero => simpa [psi_eq_cos ht] using Real.abs_cos_le_one (Real.sqrt t)
  | succ n ih =>
    rw [psi_derivative_integral n ht, abs_mul]
    rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hc := psi_smooth.continuous_iteratedDeriv n (by simp)
    calc
      (1 / 2 : ℝ) * |∫ r in (0 : ℝ)..1,
          r ^ (2 * n) * iteratedDeriv n psi (r ^ 2 * t)|
          ≤ (1 / 2 : ℝ) * ∫ r in (0 : ℝ)..1,
              |r ^ (2 * n) * iteratedDeriv n psi (r ^ 2 * t)| := by
        gcongr
        exact intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ (1 / 2 : ℝ) * ∫ r in (0 : ℝ)..1,
          r ^ (2 * n) * ((n ! : ℝ) / (2 * n)!) := by
        gcongr
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact (((continuous_id.pow _).mul
            (hc.comp ((continuous_id.pow 2).mul_const t))).abs).intervalIntegrable _ _
        · exact ((continuous_id.pow _).mul_const _).intervalIntegrable _ _
        · intro r hr
          rw [abs_mul, abs_of_nonneg (pow_nonneg hr.1 _)]
          exact mul_le_mul_of_nonneg_left (ih (mul_nonneg (sq_nonneg _) ht))
            (pow_nonneg hr.1 _)
      _ = ((n + 1)! : ℝ) / (2 * (n + 1))! := by
        rw [intervalIntegral.integral_mul_const, integral_pow]
        simp only [one_pow, zero_pow (by omega : 2 * n + 1 ≠ 0), sub_zero]
        rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        push_cast
        field_simp
        ring

/-- The entire square-sinc endpoint profile at resolution parameter `η`. -/
noncomputable def endpoint (η : ℝ) : ℝ → ℝ :=
  FormalMultilinearSeries.ofScalarsSum
    (fun k => 2 * (-1 : ℝ) ^ k * (8 / η) ^ k / (2 * k + 2)!)

private theorem endpoint_radius (η : ℝ) :
    (FormalMultilinearSeries.ofScalars ℝ
      (fun k => 2 * (-1 : ℝ) ^ k * (8 / η) ^ k / (2 * k + 2)!)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have hs := ((Real.hasSum_cosh (Real.sqrt (|8 / η| * (r : ℝ)))).summable).mul_left 2
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
  intro k
  simp only [FormalMultilinearSeries.ofScalars_norm]
  rw [pow_mul, Real.sq_sqrt (by positivity : 0 ≤ |8 / η| * (r : ℝ))]
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    Real.norm_natCast, mul_pow]
  norm_num only [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← norm_div]
  calc
    2 * ‖8 / η‖ ^ k / ↑(2 * k + 2)! * (r : ℝ) ^ k =
        2 * (|8 / η| ^ k * (r : ℝ) ^ k / ↑(2 * k + 2)!) := by
      rw [Real.norm_eq_abs]
      ring
    _ ≤ 2 * (|8 / η| ^ k * (r : ℝ) ^ k / ↑(2 * k)!) := by
      gcongr
      omega

/-- The endpoint profile is smooth on all of `ℝ`, including the origin. -/
theorem endpoint_smooth (η : ℝ) : ContDiff ℝ ⊤ (endpoint η) := by
  apply AnalyticOnNhd.contDiff
  intro t _
  apply (FormalMultilinearSeries.analyticOnNhd _)
  simp [endpoint_radius, Metric.eball_top]

/-- The endpoint is normalized at zero. -/
theorem endpoint_zero (η : ℝ) : endpoint η 0 = 1 := by
  norm_num [endpoint, FormalMultilinearSeries.ofScalarsSum_zero]

private theorem endpoint_mul (η t : ℝ) :
    (8 / η * t) * endpoint η t = 2 * (1 - psi (8 / η * t)) := by
  have hs : Summable (fun k => (-1 : ℝ) ^ k / (2 * k)! * (8 / η * t) ^ k) := by
    have h := (FormalMultilinearSeries.ofScalars ℝ
      (fun k => (-1 : ℝ) ^ k / (2 * k)!)).summable
      (x := 8 / η * t) (by simp [psi_radius, Metric.eball_top])
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using h
  have he := hs.tsum_eq_zero_add
  simp only [pow_zero, Nat.mul_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one] at he
  rw [psi, FormalMultilinearSeries.ofScalars_sum_eq] at *
  simp only [smul_eq_mul] at *
  rw [he, endpoint, FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]
  rw [← tsum_mul_left, show 2 * (1 - (1 + ∑' b : ℕ,
      (-1 : ℝ) ^ (b + 1) / ↑(2 * (b + 1))! * (8 / η * t) ^ (b + 1))) =
      -2 * ∑' b : ℕ, (-1 : ℝ) ^ (b + 1) / ↑(2 * (b + 1))! *
        (8 / η * t) ^ (b + 1) by ring, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [show 2 * (k + 1) = 2 * k + 2 by omega]
  simp only [pow_succ, mul_pow]
  ring

private theorem endpoint_eq_cos {η t : ℝ} (hη : 0 < η) (ht : 0 < t) :
    endpoint η t = 2 * (1 - Real.cos (Real.sqrt (8 / η * t))) / (8 / η * t) := by
  apply (eq_div_iff (by positivity : 8 / η * t ≠ 0)).2
  rw [mul_comm, endpoint_mul, psi_eq_cos (by positivity)]

/-- The endpoint profile is nonnegative on the nonnegative half-line. -/
theorem endpoint_nonneg {η t : ℝ} (hη : 0 < η) (ht : 0 ≤ t) :
    0 ≤ endpoint η t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · rw [endpoint_zero]; norm_num
  · rw [endpoint_eq_cos hη ht]
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.cos_le_one _)))
      (by positivity)

/-- Beyond unit distance the endpoint profile is at most half the mass parameter. -/
theorem endpoint_tail {η t : ℝ} (hη : 0 < η) (ht : 1 ≤ t) :
    endpoint η t ≤ η / 2 := by
  rw [endpoint_eq_cos hη (by linarith)]
  apply (div_le_iff₀ (by positivity : 0 < 8 / η * t)).2
  have hcos := Real.neg_one_le_cos (Real.sqrt (8 / η * t))
  have he : η / 2 * (8 / η * t) = 4 * t := by field_simp; ring
  rw [he]
  linarith


private theorem triangle_cos_integral {z : ℝ} (hz : z ≠ 0) :
    (∫ r in (0 : ℝ)..1, 2 * (1 - r) * Real.cos (r * z)) =
      2 * (1 - Real.cos z) / z ^ 2 := by
  have hd (r : ℝ) : HasDerivAt
      (fun r => 2 * ((1 - r) * Real.sin (r * z) / z - Real.cos (r * z) / z ^ 2))
      (2 * (1 - r) * Real.cos (r * z)) r := by
    have h := ((((hasDerivAt_const r 1).sub (hasDerivAt_id r)).mul
      (((hasDerivAt_id r).mul_const z).sin)).div_const z).sub
      ((((hasDerivAt_id r).mul_const z).cos).div_const (z ^ 2))
    convert! h.const_mul 2 using 1 <;> dsimp <;> field_simp <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    (((continuous_const.sub continuous_id).const_mul 2 |>.mul
      (Real.continuous_cos.comp (continuous_id.mul_const z))).intervalIntegrable 0 1)]
  simp only [sub_self, zero_mul, zero_div, one_mul, Real.sin_zero, Real.cos_zero]
  field_simp
  ring

private theorem endpoint_integral {η t : ℝ} (hη : 0 < η) (ht : 0 ≤ t) :
    endpoint η t = ∫ r in (0 : ℝ)..1, 2 * (1 - r) * psi ((8 / η * r ^ 2) * t) := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp only [endpoint_zero, mul_zero, psi_zero, mul_one]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (f := fun _ : ℝ => 1) (g := fun x : ℝ => x)
        intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
    norm_num [integral_id]
  · rw [endpoint_eq_cos hη ht]
    symm
    calc
      _ = ∫ r in (0 : ℝ)..1, 2 * (1 - r) * Real.cos (r * Real.sqrt (8 / η * t)) := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le zero_le_one] at hr
        dsimp only
        rw [psi_eq_cos (by positivity), show (8 / η * r ^ 2) * t = r ^ 2 * (8 / η * t) by ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr.1]
      _ = _ := by
        rw [triangle_cos_integral (by positivity), Real.sq_sqrt (by positivity)]

private theorem endpoint_derivative_integral {η : ℝ} (hη : 0 < η) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    iteratedDeriv n (endpoint η) t =
      ∫ r in (0 : ℝ)..1, 2 * (1 - r) * (8 / η * r ^ 2) ^ n *
        iteratedDeriv n psi ((8 / η * r ^ 2) * t) := by
  have he : EqOn (iteratedDeriv n (endpoint η))
      (fun t => ∫ r in (0 : ℝ)..1, 2 * (1 - r) * (8 / η * r ^ 2) ^ n *
        iteratedDeriv n psi ((8 / η * r ^ 2) * t)) (Ioi 0) := by
    intro t ht
    have heq : endpoint η =ᶠ[𝓝 t] (fun s =>
        ∫ r in (0 : ℝ)..1, 2 * (1 - r) * psi ((8 / η * r ^ 2) * s)) := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      exact endpoint_integral hη hs.le
    rw [heq.iteratedDeriv_eq n]
    exact congrFun (weighted_integral_iteratedDeriv (fun r => 2 * (1 - r))
      (fun r => 8 / η * r ^ 2) (by fun_prop) (by fun_prop) n) t
  have hc := psi_smooth.continuous_iteratedDeriv n (by simp)
  apply he.closure ((endpoint_smooth η).continuous_iteratedDeriv n (by simp)) ?_
    (by simpa using ht)
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((continuous_const.mul (continuous_const.sub continuous_snd)).mul
      ((continuous_const.mul (continuous_snd.pow 2)).pow _)).mul
    (hc.comp ((continuous_const.mul (continuous_snd.pow 2)).mul continuous_fst))


/-- The triangular cosine kernel gives the sharper shifted-factorial estimate. -/
private theorem endpoint_derivative_bound_sharp {η : ℝ} (hη : 0 < η) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    |iteratedDeriv n (endpoint η) t| / (n ! : ℝ) ≤
      2 * (8 / η) ^ n / (2 * n + 2)! := by
  have hc := psi_smooth.continuous_iteratedDeriv n (by simp)
  have hb : 0 < 8 / η := by positivity
  have hi : (∫ r in (0 : ℝ)..1,
      2 * (1 - r) * (8 / η * r ^ 2) ^ n * ((n ! : ℝ) / (2 * n)!)) =
      2 * (8 / η) ^ n * (n ! : ℝ) / (2 * n + 2)! := by
    calc
      _ = 2 * (8 / η) ^ n * ((n ! : ℝ) / (2 * n)!) *
          ∫ r in (0 : ℝ)..1, (r ^ (2 * n) - r ^ (2 * n + 1)) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro r _
        dsimp only
        simp only [mul_pow, ← pow_mul, pow_succ]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub
          (f := fun r : ℝ => r ^ (2 * n)) (g := fun r : ℝ => r ^ (2 * n + 1))
          ((continuous_id.pow _).intervalIntegrable _ _)
          ((continuous_id.pow _).intervalIntegrable _ _),
          integral_pow, integral_pow]
        simp only [one_pow, zero_pow (by omega : 2 * n + 1 ≠ 0),
          zero_pow (by omega : 2 * n + 1 + 1 ≠ 0), sub_zero]
        rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega]
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        push_cast
        field_simp
        ring
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n !)).2
  calc
    |iteratedDeriv n (endpoint η) t| =
        |∫ r in (0 : ℝ)..1, 2 * (1 - r) * (8 / η * r ^ 2) ^ n *
          iteratedDeriv n psi ((8 / η * r ^ 2) * t)| := by
      rw [endpoint_derivative_integral hη n ht]
    _ ≤ ∫ r in (0 : ℝ)..1, |2 * (1 - r) * (8 / η * r ^ 2) ^ n *
          iteratedDeriv n psi ((8 / η * r ^ 2) * t)| :=
      intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ r in (0 : ℝ)..1,
        2 * (1 - r) * (8 / η * r ^ 2) ^ n * ((n ! : ℝ) / (2 * n)!) := by
      apply intervalIntegral.integral_mono_on zero_le_one
      · apply Continuous.intervalIntegrable
        exact ((((continuous_const.mul (continuous_const.sub continuous_id)).mul
          ((continuous_const.mul (continuous_id.pow 2)).pow _)).mul
          (hc.comp ((continuous_const.mul (continuous_id.pow 2)).mul_const t))).abs)
      · apply Continuous.intervalIntegrable
        fun_prop
      · intro r hr
        have hw : 0 ≤ 2 * (1 - r) * (8 / η * r ^ 2) ^ n :=
          mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hr.2))
            (pow_nonneg (mul_nonneg hb.le (sq_nonneg _)) _)
        rw [abs_mul, abs_of_nonneg hw]
        exact mul_le_mul_of_nonneg_left
          (psi_derivative_bound n (mul_nonneg (mul_nonneg hb.le (sq_nonneg _)) ht)) hw
    _ = (2 * (8 / η) ^ n / ↑(2 * n + 2)!) * (n ! : ℝ) := by rw [hi]; ring

/-- The normalized all-order derivative budget for the entire endpoint profile. -/
theorem endpoint_derivative_bound {η : ℝ} (hη : 0 < η) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    |iteratedDeriv n (endpoint η) t| / (n ! : ℝ) ≤ (8 / η) ^ n / (2 * n)! := by
  apply (endpoint_derivative_bound_sharp hη n ht).trans
  have hf : (2 : ℝ) * (2 * n)! ≤ (2 * n + 2)! := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hp : (0 : ℝ) ≤ (2 * n)! := by positivity
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have he : (2 : ℝ) ≤ (2 * n + 1 + 1) * (2 * n + 1) := by nlinarith
    simpa only [Nat.cast_ofNat, mul_assoc] using mul_le_mul_of_nonneg_right he hp
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (2 * n + 2)!)
    (by positivity : (0 : ℝ) < (2 * n)!)).2
  nlinarith [mul_le_mul_of_nonneg_left hf (pow_nonneg (by positivity : (0 : ℝ) ≤ 8 / η) n)]

/-- One entire endpoint function supplies normalization, positivity, tail suppression and every
derivative budget simultaneously. -/
theorem endpoint_budget {η : ℝ} (hη : 0 < η) :
    ContDiff ℝ ⊤ (endpoint η) ∧ endpoint η 0 = 1 ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ endpoint η t) ∧
      (∀ t : ℝ, 1 ≤ t → endpoint η t ≤ η / 2) ∧
      (∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
        |iteratedDeriv n (endpoint η) t| / (n ! : ℝ) ≤ (8 / η) ^ n / (2 * n)!) :=
  ⟨endpoint_smooth η, endpoint_zero η, fun _ ht => endpoint_nonneg hη ht,
    fun _ ht => endpoint_tail hη ht, fun n _ ht => endpoint_derivative_bound hη n ht⟩


#print axioms psi_derivative_integral
#print axioms psi_derivative_bound
#print axioms endpoint_budget

end SincSquareDerivativeBudget

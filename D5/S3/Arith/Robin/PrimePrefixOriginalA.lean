/- GID: D5/S3/Arith/Robin/PrimePrefixOriginalA
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PrimePrefixOriginalA
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The literal original two-piece Phi constant is integrable and strictly below one half. -/

import D5.S3.Arith.Robin.PrimePrefixPhiCurvature
import D5.S3.Weil.Mertens.Gamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Tactic

/-!
The literal Phi and rate belong to PrimorialGlobalLaplaceEnvelope. Its finite
Ein binding is reused here. The all-real rate derivative and moment computation
are consumed copies from PrimePrefixPhiCurvature, whose derivative supplier is
PrimorialFirstOrderConcentrationCounterexample. The complete log-exponential
integrability proof and public Gamma integral supplier belong to Mertens.Gamma
(the PrimeNumberTheoremAnd port of the classical Mertens argument).

The near kernel is represented by the full finite average of the genuine Phi
curvature. The whole infinite tail is normalized with the same Euler constant,
proved absolutely integrable, and proved strictly negative. These are the literal
original two-piece A integrals from actual-prefix theory section 444.1.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter MeasureTheory
open scoped Topology Interval
namespace D5.S3.Arith.Robin.PrimePrefixOriginalA
open D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope

private noncomputable def ein (v : ℝ) : ℝ := ∫ w in (0 : ℝ)..v, rate w
private noncomputable def expTail (v : ℝ) : ℝ :=
  ∫ w : ℝ in Ioi v, Real.exp (-w) / w

private theorem continuous_rate : Continuous rate := by
  unfold rate
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop) 0 1

private theorem rate_eq {v : ℝ} (hv : v ≠ 0) :
    rate v = (1 - Real.exp (-v)) / v := by
  unfold rate
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hv)]
  simp only [mul_zero, mul_one, integral_exp, Real.exp_zero, smul_eq_mul]
  field_simp
  ring

private theorem ein_original_integral (v : ℝ) :
    ein v = ∫ b in (0 : ℝ)..1, (1 - Real.exp (-v * b)) / b := by
  by_cases hv : v = 0
  · simp [hv, ein]
  have heq : (∫ b in (0 : ℝ)..1, (1 - Real.exp (-v * b)) / b) =
      ∫ b in (0 : ℝ)..1, v * rate (v * b) := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro b hb
    change (1 - Real.exp (-v * b)) / b = v * rate (v * b)
    rw [rate_eq (mul_ne_zero hv (ne_of_gt hb.1))]
    have harg : -(v * b) = -v * b := by ring
    rw [harg]
    field_simp
  rw [heq, intervalIntegral.integral_const_mul]
  simpa [ein, smul_eq_mul] using
    (intervalIntegral.smul_integral_comp_mul_left rate (a := 0) (b := 1) v).symm

private theorem actualPhi_eq_exp_ein (v : ℝ) : actualPhi v = Real.exp (ein v) := by
  rw [ein_original_integral]
  rfl

private lemma log_integrable :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · -- On `Ioc 0 1`: dominate by `|log v|`, which is integrable.
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  · -- On `Ioi 1`: dominate by `2 * exp (-v/2)`, integrable.
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]
      -- `log v ≤ v`
      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
      -- `v ≤ 2 * exp (v/2)`
      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]
      -- combine: log v * exp(-v) ≤ v * exp(-v) ≤ 2 exp(v/2) exp(-v) = 2 exp(-v/2)
      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep

private theorem integrableOn_expTail_kernel {v : ℝ} (hv : 0 < v) :
    IntegrableOn (fun w : ℝ => Real.exp (-w) / w) (Ioi v) := by
  apply Integrable.mono' ((integrableOn_exp_neg_Ioi v).div_const v)
  · exact ((Real.measurable_exp.comp measurable_neg).div measurable_id).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with w hw
    have hwpos : 0 < w := hv.trans hw
    simp only [norm_div, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-w)),
      abs_of_pos hwpos]
    exact div_le_div_of_nonneg_left (Real.exp_pos (-w)).le hv hw.le

private theorem expTail_nonneg {v : ℝ} (hv : 0 < v) : 0 ≤ expTail v := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro w hw
  exact div_nonneg (Real.exp_pos (-w)).le (hv.trans hw).le

private theorem expTail_le {v : ℝ} (hv : 0 < v) : expTail v ≤ Real.exp (-v) / v := by
  rw [← integral_exp_neg_Ioi v, ← integral_div]
  apply setIntegral_mono_on (integrableOn_expTail_kernel hv)
    ((integrableOn_exp_neg_Ioi v).div_const v) measurableSet_Ioi
  intro w hw
  exact div_le_div_of_nonneg_left (Real.exp_pos (-w)).le hv hw.le

private theorem continuous_zero_primitive :
    Continuous (fun w : ℝ => (1 - Real.exp (-w)) * Real.log w) := by
  have heq : (fun w : ℝ => (1 - Real.exp (-w)) * Real.log w) =
      fun w : ℝ => rate w * (w * Real.log w) := by
    funext w
    by_cases hw : w = 0
    · simp [hw]
    · rw [rate_eq hw]
      field_simp
  rw [heq]
  exact continuous_rate.mul Real.continuous_mul_log

private theorem zero_primitive_hasDerivAt {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun x : ℝ => (1 - Real.exp (-x)) * Real.log x)
      (Real.log w * Real.exp (-w) + rate w) w := by
  have h := ((hasDerivAt_const w (1 : ℝ)).sub ((hasDerivAt_id w).neg.exp)).mul
    (Real.hasDerivAt_log hw.ne')
  apply h.congr_deriv
  dsimp
  rw [rate_eq hw.ne']
  field_simp
  ring

private theorem log_near_value {v : ℝ} (hv : 0 < v) :
    (∫ w in (0 : ℝ)..v, Real.log w * Real.exp (-w)) =
      (1 - Real.exp (-v)) * Real.log v - ein v := by
  have hl : IntervalIntegrable (fun w : ℝ => Real.log w * Real.exp (-w)) volume 0 v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hv.le).2
      (log_integrable.mono_set Ioc_subset_Ioi_self)
  have hr : IntervalIntegrable rate volume 0 v := continuous_rate.intervalIntegrable 0 v
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hv.le
    continuous_zero_primitive.continuousOn
    (fun w hw => zero_primitive_hasDerivAt hw.1) (hl.add hr)
  rw [intervalIntegral.integral_add hl hr] at h
  simpa only [neg_zero, Real.exp_zero, sub_self, zero_mul, sub_zero] using
    (eq_sub_iff_add_eq.mpr h :
      (∫ w in (0 : ℝ)..v, Real.log w * Real.exp (-w)) =
        (1 - Real.exp (-v)) * Real.log v - (1 - Real.exp (-0)) * Real.log 0 - ein v)

private theorem log_tail_hasDerivAt {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun x : ℝ => Real.log x * Real.exp (-x))
      (Real.exp (-w) / w - Real.log w * Real.exp (-w)) w := by
  have h := (Real.hasDerivAt_log hw.ne').mul ((hasDerivAt_id w).neg.exp)
  apply h.congr_deriv
  dsimp
  simp only [div_eq_mul_inv]
  ring

private theorem log_tail_value {v : ℝ} (hv : 0 < v) :
    (∫ w : ℝ in Ioi v, Real.log w * Real.exp (-w)) =
      Real.exp (-v) * Real.log v + expTail v := by
  have hl : IntegrableOn (fun w : ℝ => Real.log w * Real.exp (-w)) (Ioi v) :=
    log_integrable.mono_set (Ioi_subset_Ioi hv.le)
  have hd : IntegrableOn
      (fun w : ℝ => Real.exp (-w) / w - Real.log w * Real.exp (-w)) (Ioi v) :=
    (integrableOn_expTail_kernel hv).sub hl
  have hder : ∀ w ∈ Ioi v, HasDerivAt (fun x : ℝ => Real.log x * Real.exp (-x))
      (Real.exp (-w) / w - Real.log w * Real.exp (-w)) w :=
    fun w hw => log_tail_hasDerivAt (hv.trans hw)
  have ht : Tendsto (fun w : ℝ => Real.log w * Real.exp (-w)) atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hder hd hl
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (log_tail_hasDerivAt hv).continuousAt.continuousWithinAt hder hd ht
  rw [integral_sub (integrableOn_expTail_kernel hv) hl] at h
  dsimp only [expTail]
  linarith

private theorem ein_normalization {v : ℝ} (hv : 0 < v) :
    ein v = Real.log v + Real.eulerMascheroniConstant + expTail v := by
  have hsplit := intervalIntegral.integral_interval_add_Ioi log_integrable
    (log_integrable.mono_set (Ioi_subset_Ioi hv.le))
  rw [log_near_value hv, log_tail_value hv,
    integral_log_mul_exp_neg_eq_deriv_Gamma] at hsplit
  have hγ := Real.eulerMascheroniConstant_eq_neg_deriv
  nlinarith

private theorem actualPhi_euler_normalization {v : ℝ} (hv : 0 < v) :
    actualPhi v = Real.exp Real.eulerMascheroniConstant * v *
      Real.exp (∫ w : ℝ in Ioi v, Real.exp (-w) / w) := by
  rw [actualPhi_eq_exp_ein, ein_normalization hv, Real.exp_add, Real.exp_add,
    Real.exp_log hv]
  dsimp only [expTail]
  ring
/- The all-real moment/derivative helpers below are consumed copies from
   PrimePrefixPhiCurvature; the original supplier provenance is retained. -/
private def aCurv_rateMoment (v : ℝ) : ℝ :=
  ∫ b in (0 : ℝ)..1, b * Real.exp (-v * b)

private def aCurv_B (v : ℝ) : ℝ :=
  actualPhi v * (rate v ^ 2 - aCurv_rateMoment v)

private theorem aCurv_continuous_rateMoment : Continuous aCurv_rateMoment := by
  unfold aCurv_rateMoment
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop) 0 1

private theorem aCurv_continuous_actualPhi : Continuous actualPhi :=
  continuous_iff_continuousAt.mpr
    (fun v => (hasDerivAt_actualPhi v).continuousAt)

private theorem aCurv_continuous_B : Continuous aCurv_B := by
  unfold aCurv_B
  exact aCurv_continuous_actualPhi.mul
    ((continuous_rate.pow 2).sub aCurv_continuous_rateMoment)

private theorem aCurv_rate_zero : rate 0 = 1 := by
  simp [rate]

private theorem aCurv_rateMoment_zero : aCurv_rateMoment 0 = 1 / 2 := by
  norm_num [aCurv_rateMoment, integral_id]

private theorem aCurv_B_zero : aCurv_B 0 = 1 / 2 := by
  rw [aCurv_B, actualPhi_zero, aCurv_rate_zero, aCurv_rateMoment_zero]
  norm_num

/-- Original all-real rate differentiation, including its zero endpoint. -/
private theorem aCurv_hasDerivAt_rate (v : ℝ) :
    HasDerivAt rate (-aCurv_rateMoment v) v := by
  let F : ℝ → ℝ → ℝ := fun w b => Real.exp (-w * b)
  let F' : ℝ → ℝ → ℝ := fun w b => -b * Real.exp (-w * b)
  have hdiff (w b : ℝ) : HasDerivAt (fun x : ℝ => F x b) (F' w b) w := by
    have h := (((hasDerivAt_id w).neg).mul_const b).exp
    apply h.congr_deriv
    dsimp [F']
    ring
  have hmeas : ∀ᶠ w in 𝓝 v,
      AEStronglyMeasurable (F w) (volume.restrict (Ι (0 : ℝ) 1)) :=
    Filter.Eventually.of_forall (fun w =>
      (show Continuous (F w) by dsimp [F]; fun_prop).aestronglyMeasurable)
  have hint : IntervalIntegrable (F v) volume 0 1 :=
    (show Continuous (F v) by dsimp [F]; fun_prop).intervalIntegrable 0 1
  have hmeas' : AEStronglyMeasurable (F' v)
      (volume.restrict (Ι (0 : ℝ) 1)) :=
    (show Continuous (F' v) by dsimp [F']; fun_prop).aestronglyMeasurable
  have hbound : ∀ᵐ b : ℝ ∂volume,
      b ∈ Ι (0 : ℝ) 1 → ∀ w ∈ Metric.ball v 1,
        ‖F' w b‖ ≤ Real.exp (|v| + 1) := by
    apply Filter.Eventually.of_forall
    intro b hb w hw
    have hb' : b ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le zero_le_one] using hb
    have hb0 : 0 ≤ b := hb'.1.le
    have hw' : |w - v| < 1 := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hw
    have hwabs : |w| ≤ |v| + 1 := by
      have htri := abs_add_le (w - v) v
      have heq : w - v + v = w := by ring
      rw [heq] at htri
      linarith
    have hexp : -w * b ≤ |v| + 1 := by
      calc
        -w * b ≤ |w| * b := mul_le_mul_of_nonneg_right (neg_le_abs w) hb0
        _ ≤ |w| := by nlinarith [abs_nonneg w, hb'.2]
        _ ≤ |v| + 1 := hwabs
    dsimp [F']
    rw [abs_mul, abs_neg, abs_of_nonneg hb0,
      abs_of_pos (Real.exp_pos _)]
    calc
      b * Real.exp (-w * b) ≤ 1 * Real.exp (-w * b) :=
        mul_le_mul_of_nonneg_right hb'.2 (Real.exp_pos _).le
      _ ≤ Real.exp (|v| + 1) := by
        simpa only [one_mul] using Real.exp_le_exp.mpr hexp
  have hboundInt : IntervalIntegrable
      (fun _ : ℝ => Real.exp (|v| + 1)) volume 0 1 := intervalIntegrable_const
  have hdiffAE : ∀ᵐ b : ℝ ∂volume,
      b ∈ Ι (0 : ℝ) 1 → ∀ w ∈ Metric.ball v 1,
        HasDerivAt (fun x : ℝ => F x b) (F' w b) w :=
    Filter.Eventually.of_forall (fun b _ w _ => hdiff w b)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := v) (s := Metric.ball v 1)
    (bound := fun _ : ℝ => Real.exp (|v| + 1))
    (a := (0 : ℝ)) (b := 1) (μ := volume)
    (Metric.ball_mem_nhds v (by norm_num : (0 : ℝ) < 1))
    hmeas hint hmeas' hbound hboundInt hdiffAE
  change HasDerivAt (fun w : ℝ => ∫ b in (0 : ℝ)..1, Real.exp (-w * b))
    (-∫ b in (0 : ℝ)..1, b * Real.exp (-v * b)) v
  simpa only [F, F', neg_mul, intervalIntegral.integral_neg] using h.2


private theorem aCurv_hasDerivAt_phi_slope (v : ℝ) :
    HasDerivAt (fun w : ℝ => actualPhi w * rate w) (aCurv_B v) v := by
  have h := (hasDerivAt_actualPhi v).mul (aCurv_hasDerivAt_rate v)
  apply h.congr_deriv
  unfold aCurv_B
  ring

private theorem aCurv_actualPhi_second_derivative (v : ℝ) :
    deriv (deriv actualPhi) v = aCurv_B v := by
  have hfun : deriv actualPhi = fun w : ℝ => actualPhi w * rate w := by
    funext w
    exact (hasDerivAt_actualPhi w).deriv
  rw [hfun]
  exact (aCurv_hasDerivAt_phi_slope v).deriv


private def aSlope (v : ℝ) : ℝ := actualPhi v * rate v
private def aAverage (v : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, aCurv_B (v * s)
private def aNearKernel (v : ℝ) : ℝ :=
  (actualPhi v * (1 - Real.exp (-v)) - v) / v ^ 2

private theorem aSlope_zero : aSlope 0 = 1 := by
  simp [aSlope, actualPhi_zero, aCurv_rate_zero]

private theorem continuous_aAverage : Continuous aAverage := by
  unfold aAverage
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (show Continuous (fun p : ℝ × ℝ => aCurv_B (p.1 * p.2)) from
      aCurv_continuous_B.comp (continuous_fst.mul continuous_snd)) 0 1

private theorem aCurv_B_le_half {v : ℝ} (hv : 0 ≤ v) : aCurv_B v ≤ 1 / 2 := by
  rcases hv.eq_or_lt with h | h
  · rw [← h, aCurv_B_zero]
  · rw [← aCurv_actualPhi_second_derivative]
    exact (PrimePrefixPhiCurvature.result.2.2 v h).2.le

private theorem aCurv_B_lt_half {v : ℝ} (hv : 0 < v) : aCurv_B v < 1 / 2 := by
  rw [← aCurv_actualPhi_second_derivative]
  exact (PrimePrefixPhiCurvature.result.2.2 v hv).2

private theorem aAverage_le_half {v : ℝ} (hv : 0 ≤ v) : aAverage v ≤ 1 / 2 := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (show (0 : ℝ) ≤ 1 by norm_num)
    ((aCurv_continuous_B.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) volume 0 1)
    (fun s hs => aCurv_B_le_half (mul_nonneg hv hs.1))
  simpa [aAverage] using h

private theorem aAverage_lt_half {v : ℝ} (hv : 0 < v) : aAverage v < 1 / 2 := by
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (show (0 : ℝ) < 1 by norm_num)
    ((aCurv_continuous_B.comp (continuous_const.mul continuous_id)).continuousOn)
    (continuous_const.continuousOn : ContinuousOn (fun _ : ℝ => (1 / 2 : ℝ)) (Icc 0 1))
    (fun s hs => aCurv_B_le_half (mul_nonneg hv.le hs.1.le))
    (show ∃ s ∈ Icc (0 : ℝ) 1, aCurv_B (v * s) < 1 / 2 from
      ⟨1, by norm_num, by simpa using aCurv_B_lt_half hv⟩)
  simpa [aAverage] using h

private theorem aAverage_eq_slope_quotient {v : ℝ} (hv : 0 < v) :
    aAverage v = (aSlope v - 1) / v := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := v)
    (fun w _ => aCurv_hasDerivAt_phi_slope w)
    (aCurv_continuous_B.intervalIntegrable 0 v)
  have hchange := intervalIntegral.integral_comp_mul_left aCurv_B hv.ne'
    (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one, smul_eq_mul] at hchange
  change (∫ w in (0 : ℝ)..v, aCurv_B w) = aSlope v - aSlope 0 at hFTC
  rw [aSlope_zero] at hFTC
  unfold aAverage
  rw [hchange, hFTC]
  ring

private theorem aNearKernel_eq_average {v : ℝ} (hv : 0 < v) :
    aNearKernel v = aAverage v := by
  rw [aAverage_eq_slope_quotient hv]
  unfold aNearKernel aSlope
  rw [rate_eq hv.ne']
  field_simp [hv.ne']

private theorem aNear_intervalIntegrable :
    IntervalIntegrable aNearKernel volume 0 1 := by
  apply (continuous_aAverage.intervalIntegrable 0 1).congr_uIoo
  intro v hv
  have hv0 : 0 < v := by simpa only [min_eq_left zero_le_one] using hv.1
  exact (aNearKernel_eq_average hv0).symm

private theorem aNear_integral_lt_half :
    (∫ v in (0 : ℝ)..1, aNearKernel v) < 1 / 2 := by
  have heq := intervalIntegral.integral_congr_Ioo_of_le (μ := volume)
    (a := (0 : ℝ)) (b := 1) zero_le_one
    (fun v hv => aNearKernel_eq_average hv.1)
  rw [heq]
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (show (0 : ℝ) < 1 by norm_num) continuous_aAverage.continuousOn
    (continuous_const.continuousOn : ContinuousOn (fun _ : ℝ => (1 / 2 : ℝ)) (Icc 0 1))
    (fun v hv => aAverage_le_half hv.1.le)
    (show ∃ v ∈ Icc (0 : ℝ) 1, aAverage v < 1 / 2 from
      ⟨1, by norm_num, aAverage_lt_half (by norm_num)⟩)
  simpa using h
private noncomputable def tailKernel (v : ℝ) : ℝ :=
  actualPhi v * (1 - Real.exp (-v)) / v ^ 2 -
    Real.exp Real.eulerMascheroniConstant / v

private theorem tailKernel_eq {v : ℝ} (hv : 0 < v) :
    tailKernel v = Real.exp Real.eulerMascheroniConstant *
      (Real.exp (expTail v) * (1 - Real.exp (-v)) - 1) / v := by
  unfold tailKernel
  rw [actualPhi_euler_normalization hv]
  change Real.exp Real.eulerMascheroniConstant * v * Real.exp (expTail v) *
    (1 - Real.exp (-v)) / v ^ 2 - Real.exp Real.eulerMascheroniConstant / v = _
  field_simp

private theorem expTail_le_exp {v : ℝ} (hv : 1 ≤ v) :
    expTail v ≤ Real.exp (-v) :=
  (expTail_le (zero_lt_one.trans_le hv)).trans
    (div_le_self (Real.exp_pos (-v)).le hv)

private theorem expTail_le_one {v : ℝ} (hv : 1 ≤ v) : expTail v ≤ 1 :=
  (expTail_le_exp hv).trans
    (Real.exp_le_one_iff.mpr (by linarith))

private theorem tail_ratio_lt_one {v : ℝ} (hv : 1 ≤ v) :
    Real.exp (expTail v) * (1 - Real.exp (-v)) < 1 := by
  have hxpos : 0 < Real.exp (-v) := Real.exp_pos _
  have hxlt : Real.exp (-v) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hstrict := mul_lt_mul_of_pos_left (Real.one_sub_lt_exp_neg hxpos.ne')
    (Real.exp_pos (Real.exp (-v)))
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hstrict
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (expTail_le_exp hv))
    (sub_pos.mpr hxlt).le).trans_lt hstrict

private theorem tailKernel_neg {v : ℝ} (hv : 1 ≤ v) : tailKernel v < 0 := by
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  rw [tailKernel_eq hvpos]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (Real.exp_pos _) (sub_neg.mpr (tail_ratio_lt_one hv))) hvpos

private theorem tail_ratio_abs_bound {v : ℝ} (hv : 1 ≤ v) :
    |Real.exp (expTail v) * (1 - Real.exp (-v)) - 1| ≤
      2 * Real.exp 1 * Real.exp (-v) := by
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  have hEnonneg := expTail_nonneg hvpos
  have hepos : 0 < Real.exp (expTail v) := Real.exp_pos _
  have hxpos : 0 < Real.exp (-v) := Real.exp_pos _
  have hexple : Real.exp (expTail v) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (expTail_le_one hv)
  have hdiffnonneg : 0 ≤ Real.exp (expTail v) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp hEnonneg)
  have hdiff : Real.exp (expTail v) - 1 ≤ Real.exp 1 * Real.exp (-v) := by
    have h := Real.self_sub_one_le_mul_log hepos.le
    rw [Real.log_exp] at h
    exact h.trans (mul_le_mul hexple (expTail_le_exp hv) hEnonneg
      (Real.exp_pos 1).le)
  have hprod : Real.exp (expTail v) * Real.exp (-v) ≤
      Real.exp 1 * Real.exp (-v) := mul_le_mul_of_nonneg_right hexple hxpos.le
  calc
    |Real.exp (expTail v) * (1 - Real.exp (-v)) - 1| =
        |(Real.exp (expTail v) - 1) - Real.exp (expTail v) * Real.exp (-v)| := by
          congr 1
          ring
    _ ≤ |Real.exp (expTail v) - 1| +
        |Real.exp (expTail v) * Real.exp (-v)| := abs_sub _ _
    _ = (Real.exp (expTail v) - 1) +
        Real.exp (expTail v) * Real.exp (-v) := by
          rw [abs_of_nonneg hdiffnonneg, abs_of_pos (mul_pos hepos hxpos)]
    _ ≤ 2 * Real.exp 1 * Real.exp (-v) := by linarith

private theorem tailKernel_abs_bound {v : ℝ} (hv : 1 ≤ v) :
    |tailKernel v| ≤
      (2 * Real.exp Real.eulerMascheroniConstant * Real.exp 1) * Real.exp (-v) := by
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  have hCpos : 0 < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  rw [tailKernel_eq hvpos, abs_div, abs_mul, abs_of_pos hCpos, abs_of_pos hvpos]
  calc
    Real.exp Real.eulerMascheroniConstant *
        |Real.exp (expTail v) * (1 - Real.exp (-v)) - 1| / v ≤
      Real.exp Real.eulerMascheroniConstant *
        (2 * Real.exp 1 * Real.exp (-v)) / v := by
          gcongr
          exact tail_ratio_abs_bound hv
    _ = ((2 * Real.exp Real.eulerMascheroniConstant * Real.exp 1) *
        Real.exp (-v)) / v := by ring
    _ ≤ (2 * Real.exp Real.eulerMascheroniConstant * Real.exp 1) *
        Real.exp (-v) := div_le_self (by positivity) hv

private theorem measurable_tailKernel : Measurable tailKernel := by
  have hPhi : Continuous actualPhi := continuous_iff_continuousAt.mpr
    (fun v => (hasDerivAt_actualPhi v).continuousAt)
  unfold tailKernel
  fun_prop

private theorem integrableOn_tailKernel : IntegrableOn tailKernel (Ioi (1 : ℝ)) := by
  apply Integrable.mono' ((integrableOn_exp_neg_Ioi 1).const_mul
    (2 * Real.exp Real.eulerMascheroniConstant * Real.exp 1))
  · exact measurable_tailKernel.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
    rw [Real.norm_eq_abs]
    exact tailKernel_abs_bound hv.le

private theorem tail_integral_neg : (∫ v : ℝ in Ioi 1, tailKernel v) < 0 := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] fun v => -tailKernel v := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
    exact (neg_pos.mpr (tailKernel_neg hv.le)).le
  have hsupp : Function.support (fun v : ℝ => -tailKernel v) ∩ Ioi 1 = Ioi 1 := by
    ext v
    constructor
    · exact fun hv => hv.2
    · intro hv
      exact ⟨(neg_pos.mpr (tailKernel_neg hv.le)).ne', hv⟩
  have hpos : 0 < ∫ v : ℝ in Ioi 1, -tailKernel v :=
    (setIntegral_pos_iff_support_of_nonneg_ae hnonneg integrableOn_tailKernel.neg).2
      (by rw [hsupp, Real.volume_Ioi]; exact ENNReal.zero_lt_top)
  rw [integral_neg] at hpos
  exact neg_pos.mp hpos

/-- The original full two-piece constant is well-defined and strictly below one half. -/
theorem result :
    IntervalIntegrable
      (fun v : ℝ => (actualPhi v * (1 - Real.exp (-v)) - v) / v ^ 2) volume 0 1 ∧
    IntegrableOn
      (fun v : ℝ => actualPhi v * (1 - Real.exp (-v)) / v ^ 2 -
        Real.exp Real.eulerMascheroniConstant / v) (Ioi 1) ∧
    ((∫ v in (0 : ℝ)..1, (actualPhi v * (1 - Real.exp (-v)) - v) / v ^ 2) +
      (∫ v : ℝ in Ioi 1, actualPhi v * (1 - Real.exp (-v)) / v ^ 2 -
        Real.exp Real.eulerMascheroniConstant / v)) < 1 / 2 := by
  change IntervalIntegrable aNearKernel volume 0 1 ∧
    IntegrableOn tailKernel (Ioi 1) ∧
    ((∫ v in (0 : ℝ)..1, aNearKernel v) + (∫ v : ℝ in Ioi 1, tailKernel v)) < 1 / 2
  refine ⟨aNear_intervalIntegrable, integrableOn_tailKernel, ?_⟩
  linarith [aNear_integral_lt_half, tail_integral_neg]

end D5.S3.Arith.Robin.PrimePrefixOriginalA

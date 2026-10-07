/- GID: D5/S3/Arith/Robin/PrimePrefixCurvatureMoments
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PrimePrefixCurvatureMoments
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The literal Phi curvature has complete mass, first and logarithmic moments, and an exact full excess tail. -/

import D5.S3.Arith.Robin.PrimePrefixOriginalA
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
Same literal actualPhi: full curvature mass, first moment, original A logarithmic
moment, and the complete stop-loss tail. Euler/Ein/Gamma normalization helpers
are consumed copies from PrimePrefixOriginalA. Its all-real rate derivative
supplier is PrimePrefixPhiCurvature, originally supplied by
PrimorialFirstOrderConcentrationCounterexample. The frozen public curvature
and original two-piece A theorem are used directly. No desired moment identity
is assumed and no private declaration from another namespace is called.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter MeasureTheory
open scoped Topology Interval
namespace D5.S3.Arith.Robin.PrimePrefixCurvatureMoments
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

private def C : ℝ := Real.exp Real.eulerMascheroniConstant
private def slope (v : ℝ) : ℝ := actualPhi v * rate v

private theorem slope_zero : slope 0 = 1 := by
  simp [slope, actualPhi_zero, aCurv_rate_zero]

private theorem hasDerivAt_slope (v : ℝ) :
    HasDerivAt slope (aCurv_B v) v := aCurv_hasDerivAt_phi_slope v

private theorem B_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ aCurv_B v := by
  rw [← aCurv_actualPhi_second_derivative]
  rcases hv.eq_or_lt with h | h
  · rw [← h, PrimePrefixPhiCurvature.result.1]
    norm_num
  · exact (PrimePrefixPhiCurvature.result.2.2 v h).1.le

private theorem B_le_half {v : ℝ} (hv : 0 ≤ v) : aCurv_B v ≤ 1 / 2 := by
  rw [← aCurv_actualPhi_second_derivative]
  rcases hv.eq_or_lt with h | h
  · rw [← h, PrimePrefixPhiCurvature.result.1]
  · exact (PrimePrefixPhiCurvature.result.2.2 v h).2.le

private theorem expTail_le_exp {v : ℝ} (hv : 1 ≤ v) :
    expTail v ≤ Real.exp (-v) :=
  (expTail_le (zero_lt_one.trans_le hv)).trans
    (div_le_self (Real.exp_pos (-v)).le hv)

private theorem expTail_le_one {v : ℝ} (hv : 1 ≤ v) : expTail v ≤ 1 :=
  (expTail_le_exp hv).trans
    (Real.exp_le_one_iff.mpr (by linarith))

private theorem tendsto_expTail : Tendsto expTail atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ Real.tendsto_exp_neg_atTop_nhds_zero
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
    exact expTail_nonneg hv
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with v hv
    exact expTail_le_exp hv

private theorem slope_euler {v : ℝ} (hv : 0 < v) :
    slope v = C * Real.exp (expTail v) * (1 - Real.exp (-v)) := by
  unfold slope C
  rw [actualPhi_euler_normalization hv, rate_eq hv.ne']
  change Real.exp Real.eulerMascheroniConstant * v * Real.exp (expTail v) *
    ((1 - Real.exp (-v)) / v) = _
  field_simp

private theorem tendsto_slope : Tendsto slope atTop (𝓝 C) := by
  have hC : Tendsto (fun _ : ℝ => C) atTop (𝓝 C) := tendsto_const_nhds
  have h1 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have he : Tendsto (fun v : ℝ => Real.exp (expTail v)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using
      (Real.continuous_exp.tendsto 0).comp tendsto_expTail
  have h := (hC.mul he).mul
    (h1.sub Real.tendsto_exp_neg_atTop_nhds_zero)
  have h' : Tendsto (fun v : ℝ => C * Real.exp (expTail v) *
      (1 - Real.exp (-v))) atTop (𝓝 C) := by simpa using h
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
  exact (slope_euler hv).symm

private theorem primitive_eq {v : ℝ} (hv : 0 < v) :
    v * slope v - actualPhi v = -(actualPhi v * Real.exp (-v)) := by
  unfold slope
  rw [rate_eq hv.ne']
  field_simp <;> ring

private theorem tendsto_phi_exp :
    Tendsto (fun v : ℝ => actualPhi v * Real.exp (-v)) atTop (𝓝 0) := by
  have hve : Tendsto (fun v : ℝ => v * Real.exp (-v)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 zero_lt_one
  have hupper : Tendsto (fun v : ℝ => C * Real.exp 1 *
      (v * Real.exp (-v))) atTop (𝓝 0) := by
    simpa using hve.const_mul (C * Real.exp 1)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun v =>
    (mul_pos (actualPhi_pos v) (Real.exp_pos _)).le)) ?_ hupper
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with v hv
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  rw [actualPhi_euler_normalization hv0]
  change C * v * Real.exp (expTail v) * Real.exp (-v) ≤ _
  have hE := Real.exp_le_exp.mpr (expTail_le_one hv)
  calc
    C * v * Real.exp (expTail v) * Real.exp (-v) ≤
        C * v * Real.exp 1 * Real.exp (-v) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left hE (by unfold C; positivity)
    _ = C * Real.exp 1 * (v * Real.exp (-v)) := by ring

private theorem tendsto_primitive :
    Tendsto (fun v : ℝ => v * slope v - actualPhi v) atTop (𝓝 0) := by
  have h : Tendsto (fun v : ℝ => -(actualPhi v * Real.exp (-v))) atTop (𝓝 0) := by
    simpa using tendsto_phi_exp.neg
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
  exact (primitive_eq hv).symm

private theorem hasDerivAt_primitive (v : ℝ) :
    HasDerivAt (fun w : ℝ => w * slope w - actualPhi w) (v * aCurv_B v) v := by
  have h := ((hasDerivAt_id v).mul (hasDerivAt_slope v)).sub
    (hasDerivAt_actualPhi v)
  apply h.congr_deriv
  change 1 * slope v + v * aCurv_B v - slope v = _
  ring

private theorem B_integrable : IntegrableOn aCurv_B (Ioi (0 : ℝ)) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun v _ => hasDerivAt_slope v) (fun v hv => B_nonneg hv.le) tendsto_slope

private theorem B_mass : (∫ v : ℝ in Ioi 0, aCurv_B v) = C - 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun v _ => hasDerivAt_slope v) (fun v hv => B_nonneg hv.le) tendsto_slope
  simpa only [slope_zero] using h

private theorem moment_integrable :
    IntegrableOn (fun v : ℝ => v * aCurv_B v) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun v _ => hasDerivAt_primitive v)
    (fun v hv => mul_nonneg hv.le (B_nonneg hv.le)) tendsto_primitive

private theorem B_first_moment :
    (∫ v : ℝ in Ioi 0, v * aCurv_B v) = 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun v _ => hasDerivAt_primitive v)
    (fun v hv => mul_nonneg hv.le (B_nonneg hv.le)) tendsto_primitive
  simpa only [zero_mul, actualPhi_zero, zero_sub, sub_neg_eq_add, zero_add] using h

private theorem stopLoss {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun v : ℝ => (v - t) * aCurv_B v) (Ioi t) ∧
    (∫ v : ℝ in Ioi t, (v - t) * aCurv_B v) = actualPhi t - C * t := by
  let P : ℝ → ℝ := fun v => (v - t) * slope v - actualPhi v
  have hder (v : ℝ) : HasDerivAt P ((v - t) * aCurv_B v) v := by
    have h := (((hasDerivAt_id v).sub_const t).mul (hasDerivAt_slope v)).sub
      (hasDerivAt_actualPhi v)
    apply h.congr_deriv
    change 1 * slope v + (v - t) * aCurv_B v - slope v = _
    ring
  have htop : Tendsto P atTop (𝓝 (-(t * C))) := by
    have h := tendsto_primitive.sub (tendsto_slope.const_mul t)
    have h' : Tendsto (fun v : ℝ => (v * slope v - actualPhi v) - t * slope v)
        atTop (𝓝 (-(t * C))) := by simpa using h
    apply h'.congr'
    filter_upwards with v
    dsimp [P]
    ring
  have hpos (v : ℝ) (hv : v ∈ Ioi t) : 0 ≤ (v - t) * aCurv_B v :=
    mul_nonneg (sub_nonneg.mpr hv.le) (B_nonneg (ht.trans hv.le))
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' (fun v _ => hder v) hpos htop, ?_⟩
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (fun v _ => hder v) hpos htop
  simpa [P, sub_eq_add_neg, add_comm, mul_comm] using h

private theorem B_log_integrable :
    IntegrableOn (fun v : ℝ => Real.log v * aCurv_B v) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) := by
      have h := intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at h
    apply Integrable.mono' (hlog.norm.const_mul (1 / 2 : ℝ))
    · exact (Real.measurable_log.mul aCurv_continuous_B.measurable).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      simp only [norm_mul, Real.norm_eq_abs]
      rw [abs_of_nonneg (B_nonneg hv.1.le)]
      exact (mul_le_mul_of_nonneg_left (B_le_half hv.1.le)
        (abs_nonneg (Real.log v))).trans_eq (by ring)
  · apply Integrable.mono' (moment_integrable.mono_set
      (Ioi_subset_Ioi (zero_le_one' ℝ)))
    · exact (Real.measurable_log.mul aCurv_continuous_B.measurable).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv0 : 0 < v := zero_lt_one.trans hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg hv.le), abs_of_nonneg (B_nonneg hv0.le)]
      have hlv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hv0).trans (by linarith)
      exact mul_le_mul_of_nonneg_right hlv (B_nonneg hv0.le)

private def nearQ (v : ℝ) : ℝ := (slope v - 1) / v
private def tailQ (v : ℝ) : ℝ := (slope v - C) / v

private theorem nearQ_eq {v : ℝ} (hv : 0 < v) :
    nearQ v = (actualPhi v * (1 - Real.exp (-v)) - v) / v ^ 2 := by
  unfold nearQ slope
  rw [rate_eq hv.ne']
  field_simp

private theorem tailQ_eq {v : ℝ} (hv : 0 < v) :
    tailQ v = actualPhi v * (1 - Real.exp (-v)) / v ^ 2 -
      Real.exp Real.eulerMascheroniConstant / v := by
  unfold tailQ slope C
  rw [rate_eq hv.ne']
  field_simp

private theorem nearQ_integrable : IntervalIntegrable nearQ volume 0 1 := by
  apply PrimePrefixOriginalA.result.1.congr_uIoo
  intro v hv
  have hv0 : 0 < v := by simpa only [min_eq_left zero_le_one] using hv.1
  exact (nearQ_eq hv0).symm

private theorem tailQ_integrable : IntegrableOn tailQ (Ioi (1 : ℝ)) := by
  apply PrimePrefixOriginalA.result.2.1.congr_fun _ measurableSet_Ioi
  intro v hv
  exact (tailQ_eq (zero_lt_one.trans hv)).symm

private def slopeAverage (v : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, aCurv_B (v * s)

private theorem continuous_slopeAverage : Continuous slopeAverage := by
  unfold slopeAverage
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (show Continuous (fun p : ℝ × ℝ => aCurv_B (p.1 * p.2)) from
      aCurv_continuous_B.comp (continuous_fst.mul continuous_snd)) 0 1

private theorem slopeAverage_eq {v : ℝ} (hv : v ≠ 0) :
    slopeAverage v = (slope v - 1) / v := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := v) (fun w _ => hasDerivAt_slope w)
    (aCurv_continuous_B.intervalIntegrable 0 v)
  have hchange := intervalIntegral.integral_comp_mul_left aCurv_B hv
    (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one, smul_eq_mul] at hchange
  rw [slope_zero] at hFTC
  unfold slopeAverage
  rw [hchange, hFTC]
  ring

private theorem nearPrimitive_continuous :
    Continuous (fun v : ℝ => (slope v - 1) * Real.log v) := by
  have heq : (fun v : ℝ => (slope v - 1) * Real.log v) =
      fun v : ℝ => slopeAverage v * (v * Real.log v) := by
    funext v
    by_cases hv : v = 0
    · simp [hv, slope_zero]
    · rw [slopeAverage_eq hv]
      field_simp
  rw [heq]
  exact continuous_slopeAverage.mul Real.continuous_mul_log

private theorem nearPrimitive_deriv {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w : ℝ => (slope w - 1) * Real.log w)
      (Real.log v * aCurv_B v + nearQ v) v := by
  have h := ((hasDerivAt_slope v).sub_const 1).mul (Real.hasDerivAt_log hv.ne')
  apply h.congr_deriv
  unfold nearQ
  ring

private theorem near_log_identity :
    (∫ v in (0 : ℝ)..1, Real.log v * aCurv_B v) +
      (∫ v in (0 : ℝ)..1, nearQ v) = 0 := by
  have hl : IntervalIntegrable (fun v : ℝ => Real.log v * aCurv_B v) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      (B_log_integrable.mono_set Ioc_subset_Ioi_self)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    nearPrimitive_continuous.continuousOn (fun v hv => nearPrimitive_deriv hv.1)
    (hl.add nearQ_integrable)
  rw [intervalIntegral.integral_add hl nearQ_integrable] at h
  simpa only [Real.log_one, mul_zero, Real.log_zero, sub_self] using h

/- The consumed full slope-tail bound is the tail-ratio helper in
   PrimePrefixOriginalA, with its product interpreted as the literal slope. -/
private theorem slope_tail_bound {v : ℝ} (hv : 1 ≤ v) :
    |slope v - C| ≤ (2 * C * Real.exp 1) * Real.exp (-v) := by
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
  have hratio : |Real.exp (expTail v) * (1 - Real.exp (-v)) - 1| ≤
      2 * Real.exp 1 * Real.exp (-v) := by
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
  rw [slope_euler hvpos]
  have heq : C * Real.exp (expTail v) * (1 - Real.exp (-v)) - C =
      C * (Real.exp (expTail v) * (1 - Real.exp (-v)) - 1) := by ring
  have hCpos : 0 < C := Real.exp_pos _
  rw [heq, abs_mul, abs_of_pos hCpos]
  exact (mul_le_mul_of_nonneg_left hratio hCpos.le).trans_eq (by ring)

private theorem tailPrimitive_integrable :
    IntegrableOn (fun v : ℝ => (slope v - C) * Real.log v) (Ioi 1) := by
  apply Integrable.mono' ((log_integrable.mono_set
    (Ioi_subset_Ioi zero_le_one)).norm.const_mul (2 * C * Real.exp 1))
  · have hs : Continuous slope := continuous_iff_continuousAt.mpr
      (fun v => (hasDerivAt_slope v).continuousAt)
    exact ((hs.measurable.sub measurable_const).mul Real.measurable_log).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
    simp only [norm_mul, Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos _)]
    calc
      |slope v - C| * |Real.log v| ≤
          ((2 * C * Real.exp 1) * Real.exp (-v)) * |Real.log v| :=
        mul_le_mul_of_nonneg_right (slope_tail_bound hv.le) (abs_nonneg _)
      _ = (2 * C * Real.exp 1) * (|Real.log v| * Real.exp (-v)) := by ring

private theorem tailPrimitive_deriv {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w : ℝ => (slope w - C) * Real.log w)
      (Real.log v * aCurv_B v + tailQ v) v := by
  have h := ((hasDerivAt_slope v).sub_const C).mul (Real.hasDerivAt_log hv.ne')
  apply h.congr_deriv
  unfold tailQ
  ring

private theorem tail_log_identity :
    (∫ v : ℝ in Ioi 1, Real.log v * aCurv_B v) +
      (∫ v : ℝ in Ioi 1, tailQ v) = 0 := by
  have hl := B_log_integrable.mono_set (Ioi_subset_Ioi zero_le_one)
  have hd : IntegrableOn (fun v : ℝ => Real.log v * aCurv_B v + tailQ v) (Ioi 1) :=
    hl.add tailQ_integrable
  have hder : ∀ v ∈ Ioi (1 : ℝ),
      HasDerivAt (fun w : ℝ => (slope w - C) * Real.log w)
        (Real.log v * aCurv_B v + tailQ v) v :=
    fun v hv => tailPrimitive_deriv (zero_lt_one.trans hv)
  have ht := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hder hd tailPrimitive_integrable
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (tailPrimitive_deriv zero_lt_one).continuousAt.continuousWithinAt hder hd ht
  rw [integral_add hl tailQ_integrable] at h
  simpa only [Real.log_one, mul_zero, sub_zero] using h

private theorem A_log_identity :
    ((∫ v in (0 : ℝ)..1,
        (actualPhi v * (1 - Real.exp (-v)) - v) / v ^ 2) +
      (∫ v : ℝ in Ioi 1, actualPhi v * (1 - Real.exp (-v)) / v ^ 2 -
        Real.exp Real.eulerMascheroniConstant / v)) =
      -(∫ v : ℝ in Ioi 0, Real.log v * aCurv_B v) := by
  have hnear : (∫ v in (0 : ℝ)..1,
      (actualPhi v * (1 - Real.exp (-v)) - v) / v ^ 2) =
      ∫ v in (0 : ℝ)..1, nearQ v := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro v hv
    exact (nearQ_eq hv.1).symm
  have htail : (∫ v : ℝ in Ioi 1,
      actualPhi v * (1 - Real.exp (-v)) / v ^ 2 -
        Real.exp Real.eulerMascheroniConstant / v) = ∫ v : ℝ in Ioi 1, tailQ v := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    exact (tailQ_eq (zero_lt_one.trans hv)).symm
  rw [hnear, htail]
  have hsplit := intervalIntegral.integral_interval_add_Ioi B_log_integrable
    (B_log_integrable.mono_set (Ioi_subset_Ioi zero_le_one))
  linarith [near_log_identity, tail_log_identity]

/-- Full literal curvature moments, the original two-piece A, and the full stop-loss tail. -/
theorem result :
    IntegrableOn (deriv (deriv actualPhi)) (Ioi (0 : ℝ)) ∧
    IntegrableOn (fun v : ℝ => v * deriv (deriv actualPhi) v) (Ioi 0) ∧
    (∫ v : ℝ in Ioi 0, deriv (deriv actualPhi) v) =
      Real.exp Real.eulerMascheroniConstant - 1 ∧
    (∫ v : ℝ in Ioi 0, v * deriv (deriv actualPhi) v) = 1 ∧
    IntegrableOn (fun v : ℝ => Real.log v * deriv (deriv actualPhi) v) (Ioi 0) ∧
    ((∫ v in (0 : ℝ)..1,
        (actualPhi v * (1 - Real.exp (-v)) - v) / v ^ 2) +
      (∫ v : ℝ in Ioi 1, actualPhi v * (1 - Real.exp (-v)) / v ^ 2 -
        Real.exp Real.eulerMascheroniConstant / v)) =
      -(∫ v : ℝ in Ioi 0, Real.log v * deriv (deriv actualPhi) v) ∧
    (∀ t : ℝ, 0 ≤ t →
      IntegrableOn (fun v : ℝ => (v - t) * deriv (deriv actualPhi) v) (Ioi t) ∧
      (∫ v : ℝ in Ioi t, (v - t) * deriv (deriv actualPhi) v) =
        actualPhi t - Real.exp Real.eulerMascheroniConstant * t) := by
  have hfun : deriv (deriv actualPhi) = aCurv_B := by
    funext v
    exact aCurv_actualPhi_second_derivative v
  rw [hfun]
  exact ⟨B_integrable, moment_integrable, B_mass, B_first_moment,
    B_log_integrable, A_log_identity, fun t ht => stopLoss ht⟩

end D5.S3.Arith.Robin.PrimePrefixCurvatureMoments

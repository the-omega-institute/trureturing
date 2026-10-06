/- GID: D5/S3/Arith/Robin/PrimorialFirstOrderConcentrationCounterexample
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PrimorialFirstOrderConcentrationCounterexample
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: A positive decreasing first-order perturbation of the original Phi has a divergent exactly compensated signed integral. -/

import D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A concentration counterexample for first-order control of the original profile.
The owner only supplies its existing rate, rate_le_one, and the public literal
actualPhi calculus bridges. No actual prime curvature or Q7 is imported.
The original-Phi construction is the counterexample; every generic calculus
helper below is consumed inside this host and has no independent freeze claim.
-/

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped BigOperators Topology Interval
open D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope

namespace D5.S3.Arith.Robin.PrimorialFirstOrderConcentrationCounterexample

def concentrationScale (ε : ℝ) : ℝ := Real.exp (-1 / ε ^ 2)
def concentratedLog (ε δ v : ℝ) : ℝ := ε * δ * (1 - Real.exp (-v / δ))
def concentratedSlope (ε δ v : ℝ) : ℝ := rate v + ε * Real.exp (-v / δ)
def perturbedRatio (ε δ v : ℝ) : ℝ := actualPhi v * Real.exp (concentratedLog ε δ v)
def originalNumerator (v : ℝ) : ℝ := actualPhi v - 1 - v
def perturbedNumerator (ε δ v : ℝ) : ℝ :=
  perturbedRatio ε δ v - 1 - concentratedSlope ε δ 0 * v
def errorNumerator (ε δ v : ℝ) : ℝ :=
  perturbedNumerator ε δ v - originalNumerator v
def errorIntegrand (ε δ σ v : ℝ) : ℝ :=
  Real.exp (-σ * v) * errorNumerator ε δ v / v ^ 2
def errorIntegral (ε δ σ : ℝ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), errorIntegrand ε δ σ v
private def splitMultiplier : ℝ := 8 * Real.exp 1

private def profileCurvature (v : ℝ) : ℝ :=
  ∫ b in (0 : ℝ)..1, b * Real.exp (-v * b)

private theorem rate_zero : rate 0 = 1 := by
  simp [rate]

private theorem rate_nonneg (v : ℝ) : 0 ≤ rate v := by
  unfold rate
  exact intervalIntegral.integral_nonneg_of_forall zero_le_one
    (fun b => (Real.exp_pos (-v * b)).le)

private theorem rate_bounds {v : ℝ} (hv : 0 ≤ v) : 0 ≤ rate v ∧ rate v ≤ 1 :=
  ⟨rate_nonneg v, rate_le_one hv⟩

private theorem profileCurvature_nonneg (v : ℝ) : 0 ≤ profileCurvature v := by
  unfold profileCurvature
  apply intervalIntegral.integral_nonneg zero_le_one
  intro b hb
  exact mul_nonneg hb.1 (Real.exp_pos _).le

private theorem profileCurvature_le_half {v : ℝ} (hv : 0 ≤ v) :
    profileCurvature v ≤ 1 / 2 := by
  have h := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
    (μ := volume) (f := fun b => b * Real.exp (-v * b)) (g := fun b => b)
    zero_le_one
    ((show Continuous (fun b : ℝ => b * Real.exp (-v * b)) by
      fun_prop).intervalIntegrable 0 1)
    (continuous_id.intervalIntegrable 0 1)
    (fun b hb => by
      have he : Real.exp (-v * b) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [hb.1])
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he hb.1)
  simpa [profileCurvature, integral_id] using h

private theorem profileCurvature_bounds {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ profileCurvature v ∧ profileCurvature v ≤ 1 / 2 :=
  ⟨profileCurvature_nonneg v, profileCurvature_le_half hv⟩

/-- Differentiation of the original literal rate, including the zero endpoint. -/
private theorem hasDerivAt_rate (v : ℝ) :
    HasDerivAt rate (-profileCurvature v) v := by
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

private theorem exact_zero_quadratic_bound
    (f g h : ℝ → ℝ) {v C : ℝ} (hv : 0 ≤ v)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfg : ∀ w ∈ Icc (0 : ℝ) v, HasDerivAt f (g w) w)
    (hgh : ∀ w ∈ Icc (0 : ℝ) v, HasDerivAt g (h w) w)
    (hC : ∀ w ∈ Icc (0 : ℝ) v, ‖h w‖ ≤ C) :
    |f v| ≤ C * v ^ 2 / 2 := by
  have hgb : ∀ w ∈ Icc (0 : ℝ) v, ‖g w‖ ≤ C * w := by
    intro w hw
    have hdiff : ∀ t ∈ Icc (0 : ℝ) w, DifferentiableAt ℝ g t :=
      fun t ht => (hgh t ⟨ht.1, ht.2.trans hw.2⟩).differentiableAt
    have hbound : ∀ t ∈ Icc (0 : ℝ) w, ‖deriv g t‖ ≤ C := by
      intro t ht
      rw [(hgh t ⟨ht.1, ht.2.trans hw.2⟩).deriv]
      exact hC t ⟨ht.1, ht.2.trans hw.2⟩
    have hm := (convex_Icc (0 : ℝ) w).norm_image_sub_le_of_norm_deriv_le
      hdiff hbound (x := 0) (y := w) ⟨le_rfl, hw.1⟩ ⟨hw.1, le_rfl⟩
    simpa only [hg0, sub_zero, Real.norm_eq_abs, abs_of_nonneg hw.1] using hm
  have hgc : ContinuousOn g (Icc (0 : ℝ) v) :=
    fun w hw => (hgh w hw).continuousAt.continuousWithinAt
  have hgI := hgc.intervalIntegrable_of_Icc (μ := volume) hv
  have hFTC : (∫ w in (0 : ℝ)..v, g w) = f v := by
    have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := f) (f' := g) (fun w hw => hfg w (by
        simpa only [uIcc_of_le hv] using hw)) hgI
    simpa only [hf0, sub_zero] using ht
  have hn : ‖∫ w in (0 : ℝ)..v, g w‖ ≤ ∫ w in (0 : ℝ)..v, C * w :=
    intervalIntegral.norm_integral_le_of_norm_le hv
      (Filter.Eventually.of_forall (fun w hw => hgb w ⟨hw.1.le, hw.2⟩))
      ((continuous_const.mul continuous_id).intervalIntegrable 0 v)
  rw [hFTC, Real.norm_eq_abs, intervalIntegral.integral_const_mul, integral_id] at hn
  simpa [mul_div_assoc] using hn

private theorem exp_moment_integrable {q : ℝ} (hq : 0 < q) (n : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ n * Real.exp (-q * v)) (Ioi 0) := by
  have hG : IntegrableOn (fun v : ℝ => Real.exp (-v) * v ^ n) (Ioi 0) := by
    simpa [Real.rpow_natCast] using
      Real.GammaIntegral_convergent (s := (n : ℝ) + 1) (by positivity)
  have hs : IntegrableOn (fun v : ℝ =>
      Real.exp (-(q * v)) * (q * v) ^ n) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff
      (fun v : ℝ => Real.exp (-v) * v ^ n) 0 hq).mpr (by simpa using hG)
  apply IntegrableOn.congr_fun (hs.const_mul ((q ^ n)⁻¹)) _ measurableSet_Ioi
  intro v hv
  change (q ^ n)⁻¹ * (Real.exp (-(q * v)) * (q * v) ^ n) =
    v ^ n * Real.exp (-q * v)
  rw [mul_pow, neg_mul]
  have hn : q ^ n ≠ 0 := pow_ne_zero n hq.ne'
  field_simp [hn] <;> ring


private theorem concentratedLog_zero (ε δ : ℝ) : concentratedLog ε δ 0 = 0 := by
  simp [concentratedLog]

private theorem concentratedSlope_zero (ε δ : ℝ) :
    concentratedSlope ε δ 0 = 1 + ε := by
  simp [concentratedSlope, rate_zero]

private theorem perturbedRatio_zero (ε δ : ℝ) : perturbedRatio ε δ 0 = 1 := by
  simp [perturbedRatio, concentratedLog_zero, actualPhi_zero]

private theorem concentratedLog_bounds {ε δ v : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hv : 0 ≤ v) :
    0 ≤ concentratedLog ε δ v ∧
      concentratedLog ε δ v ≤ ε * δ ∧
      concentratedLog ε δ v ≤ ε * v := by
  have hx : -v / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  have he := Real.exp_le_one_iff.mpr hx
  have htan := Real.add_one_le_exp (-v / δ)
  simp only [neg_div] at htan
  constructor
  · unfold concentratedLog
    exact mul_nonneg (mul_nonneg hε hδ.le) (sub_nonneg.mpr he)
  constructor
  · unfold concentratedLog
    have hm := mul_le_mul_of_nonneg_left (sub_le_self 1 (Real.exp_pos (-v / δ)).le)
      (mul_nonneg hε hδ.le)
    simpa only [mul_one] using hm
  · unfold concentratedLog
    have hm := mul_le_mul_of_nonneg_left
      (show 1 - Real.exp (-v / δ) ≤ v / δ by rw [neg_div]; linarith) (mul_nonneg hε hδ.le)
    calc
      _ ≤ (ε * δ) * (v / δ) := hm
      _ = ε * v := by field_simp [hδ.ne'] <;> ring

private theorem hasDerivAt_concentratedLog {ε δ v : ℝ} (hδ : δ ≠ 0) :
    HasDerivAt (concentratedLog ε δ) (ε * Real.exp (-v / δ)) v := by
  have h := ((((hasDerivAt_id v).neg).div_const δ).exp).const_sub (1 : ℝ)
  have hh := h.const_mul (ε * δ)
  apply hh.congr_deriv
  simp only [Pi.neg_apply, id_eq]
  field_simp [hδ] <;> ring

private theorem hasDerivAt_concentratedSlope {ε δ v : ℝ} (hδ : δ ≠ 0) :
    HasDerivAt (concentratedSlope ε δ)
      (-profileCurvature v - (ε / δ) * Real.exp (-v / δ)) v := by
  have he := ((((hasDerivAt_id v).neg).div_const δ).exp).const_mul ε
  have h := (hasDerivAt_rate v).add he
  apply h.congr_deriv
  simp only [Pi.neg_apply, id_eq]
  ring

private theorem hasDerivAt_perturbedRatio {ε δ v : ℝ} (hδ : δ ≠ 0) :
    HasDerivAt (perturbedRatio ε δ)
      (perturbedRatio ε δ v * concentratedSlope ε δ v) v := by
  have h := (hasDerivAt_actualPhi v).mul (hasDerivAt_concentratedLog (ε := ε) hδ).exp
  apply h.congr_deriv
  unfold perturbedRatio concentratedSlope
  ring

private theorem perturbedSlope_antitone {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) :
    Antitone (concentratedSlope ε δ) := by
  apply antitone_of_hasDerivAt_nonpos (fun v => hasDerivAt_concentratedSlope (ε := ε) (v := v) hδ.ne')
  intro v
  change -profileCurvature v - (ε / δ) * Real.exp (-v / δ) ≤ (0 : ℝ)
  have hj := profileCurvature_nonneg v
  have hx := mul_nonneg (div_nonneg hε hδ.le) (Real.exp_pos (-v / δ)).le
  linarith

private theorem perturbed_first_order {ε δ v : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hv : 0 ≤ v) :
    0 < perturbedRatio ε δ v ∧
      Real.exp (-ε * v) * actualPhi v ≤ perturbedRatio ε δ v ∧
      perturbedRatio ε δ v ≤ Real.exp (ε * v) * actualPhi v ∧
      |concentratedSlope ε δ v - rate v| ≤ ε ∧
      0 ≤ concentratedSlope ε δ v := by
  have hh := concentratedLog_bounds hε hδ hv
  have he1 : 1 ≤ Real.exp (concentratedLog ε δ v) := Real.one_le_exp hh.1
  have he0 : Real.exp (-ε * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have heup := Real.exp_le_exp.mpr hh.2.2
  have hφ := (actualPhi_pos v).le
  have hex : Real.exp (-v / δ) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
  refine ⟨mul_pos (actualPhi_pos v) (Real.exp_pos _), ?_, ?_, ?_, ?_⟩
  · unfold perturbedRatio
    nlinarith [mul_le_mul_of_nonneg_right he0 hφ,
      mul_le_mul_of_nonneg_left he1 hφ]
  · unfold perturbedRatio
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left heup hφ
  · unfold concentratedSlope
    rw [add_sub_cancel_left, abs_of_nonneg (mul_nonneg hε (Real.exp_pos _).le)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hex hε
  · unfold concentratedSlope
    exact add_nonneg (rate_nonneg v) (mul_nonneg hε (Real.exp_pos _).le)

private theorem errorNumerator_eq (ε δ v : ℝ) :
    errorNumerator ε δ v =
      actualPhi v * (Real.exp (concentratedLog ε δ v) - 1) - ε * v := by
  unfold errorNumerator perturbedNumerator originalNumerator perturbedRatio
  rw [concentratedSlope_zero]
  ring

private theorem errorNumerator_zero (ε δ : ℝ) : errorNumerator ε δ 0 = 0 := by
  rw [errorNumerator_eq, concentratedLog_zero]
  simp

private theorem hasDerivAt_errorNumerator {ε δ v : ℝ} (hδ : δ ≠ 0) :
    HasDerivAt (errorNumerator ε δ)
      (perturbedRatio ε δ v * concentratedSlope ε δ v - actualPhi v * rate v - ε) v := by
  have h := ((hasDerivAt_perturbedRatio (ε := ε) hδ).sub (hasDerivAt_actualPhi v)).sub
    ((hasDerivAt_id v).const_mul ε)
  have hh := h.congr_deriv (show
    perturbedRatio ε δ v * concentratedSlope ε δ v - actualPhi v * rate v - ε * 1 =
    perturbedRatio ε δ v * concentratedSlope ε δ v - actualPhi v * rate v - ε by ring)
  apply hh.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro w
  simp only [Pi.sub_apply, id_eq]
  rw [errorNumerator_eq]
  unfold perturbedRatio
  ring

private theorem hasDerivAt_errorNumerator_zero {ε δ : ℝ} (hδ : δ ≠ 0) :
    HasDerivAt (errorNumerator ε δ) 0 0 := by
  have h := hasDerivAt_errorNumerator (ε := ε) (v := 0) hδ
  apply h.congr_deriv
  rw [perturbedRatio_zero, concentratedSlope_zero, actualPhi_zero, rate_zero]
  ring

private theorem error_second_derivative {ε δ v : ℝ} (hδ : δ ≠ 0) :
    HasDerivAt
      (fun w => perturbedRatio ε δ w * concentratedSlope ε δ w -
        actualPhi w * rate w - ε)
      (perturbedRatio ε δ v *
          (concentratedSlope ε δ v ^ 2 - profileCurvature v -
            (ε / δ) * Real.exp (-v / δ)) -
        actualPhi v * (rate v ^ 2 - profileCurvature v)) v := by
  have h := ((hasDerivAt_perturbedRatio (ε := ε) hδ).mul
    (hasDerivAt_concentratedSlope (ε := ε) hδ)).sub
      ((hasDerivAt_actualPhi v).mul (hasDerivAt_rate v))
  have hh := h.sub_const ε
  apply hh.congr_deriv
  ring

private theorem phi_le_exp_self {v : ℝ} (hv : 0 ≤ v) : actualPhi v ≤ Real.exp v := by
  let f : ℝ → ℝ := fun w => Real.exp (-w) * actualPhi w
  have hd (w : ℝ) : HasDerivAt f (f w * (rate w - 1)) w := by
    have h := ((hasDerivAt_id w).neg.exp).mul (hasDerivAt_actualPhi w)
    apply h.congr_deriv
    dsimp [f]
    ring
  have hc : ContinuousOn f (Ici 0) := fun w hw => (hd w).continuousAt.continuousWithinAt
  have hm : AntitoneOn f (Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ)) hc
      (fun w hw => (hd w).differentiableAt.differentiableWithinAt)
      (fun w hw => by
        rw [(hd w).deriv]
        have hw0 : 0 ≤ w := (interior_subset hw)
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (Real.exp_pos _).le (actualPhi_pos w).le)
          (sub_nonpos.mpr (rate_le_one hw0)))
  have hb : f v ≤ 1 := by
    have h := hm (by simp) hv hv
    simpa [f, actualPhi_zero] using h
  have hh := mul_le_mul_of_nonneg_right hb (Real.exp_pos v).le
  have he : Real.exp (-v) * Real.exp v = 1 := by rw [← Real.exp_add]; simp
  have heq : f v * Real.exp v = actualPhi v := by
    dsimp [f]
    calc
      _ = (Real.exp (-v) * Real.exp v) * actualPhi v := by ring
      _ = actualPhi v := by rw [he, one_mul]
  simpa only [heq, one_mul] using hh

private theorem phi_sub_one_local {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    actualPhi v - 1 ≤ Real.exp 1 * v := by
  have hb : ∀ w ∈ Icc (0 : ℝ) v, ‖deriv actualPhi w‖ ≤ Real.exp 1 := by
    intro w hw
    rw [(hasDerivAt_actualPhi w).deriv, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (actualPhi_pos w).le (rate_nonneg w))]
    have hφ : actualPhi w ≤ Real.exp 1 :=
      (phi_le_exp_self hw.1).trans (Real.exp_le_exp.mpr (hw.2.trans hv1))
    simpa only [mul_one] using
      mul_le_mul hφ (rate_le_one hw.1) (rate_nonneg w) (Real.exp_pos 1).le
  have hm := (convex_Icc (0 : ℝ) v).norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (hasDerivAt_actualPhi w).differentiableAt) hb
    (x := 0) (y := v) ⟨le_rfl, hv⟩ ⟨hv, le_rfl⟩
  rw [actualPhi_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg hv] at hm
  exact (le_abs_self _).trans hm

private theorem perturbed_local_upper {ε δ v : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    errorNumerator ε δ v ≤ 2 * Real.exp 1 * ε * v ^ 2 := by
  let h : ℝ := concentratedLog ε δ v
  have hb := concentratedLog_bounds hε hδ hv
  have hh0 : 0 ≤ h := hb.1
  have hhv : h ≤ ε * v := hb.2.2
  have hh1 : |h| ≤ 1 := by
    rw [abs_of_nonneg hh0]
    have hm := mul_le_mul hε1 hv1 hv (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have hrem := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hh1)).2
  have hφ : actualPhi v ≤ Real.exp 1 :=
    (phi_le_exp_self hv).trans (Real.exp_le_exp.mpr hv1)
  have hφ0 := (actualPhi_pos v).le
  have hp := phi_sub_one_local hv hv1
  have hs : h ^ 2 ≤ ε ^ 2 * v ^ 2 := by
    have hm := mul_le_mul hhv hhv hh0 (mul_nonneg hε hv)
    nlinarith
  rw [errorNumerator_eq]
  have hid : actualPhi v * (Real.exp h - 1) - ε * v =
      actualPhi v * (Real.exp h - 1 - h) +
        (actualPhi v - 1) * h + (h - ε * v) := by ring
  change actualPhi v * (Real.exp h - 1) - ε * v ≤ _
  rw [hid]
  have hA := mul_le_mul_of_nonneg_left hrem hφ0
  have hA' := mul_le_mul_of_nonneg_right hφ (sq_nonneg h)
  have hB := mul_le_mul_of_nonneg_right hp hh0
  have hB' := mul_le_mul_of_nonneg_left hhv (mul_nonneg (Real.exp_pos 1).le hv)
  have hA'' := mul_le_mul_of_nonneg_left hs (Real.exp_pos 1).le
  have heps : ε ^ 2 ≤ ε := by nlinarith
  nlinarith [mul_nonneg (Real.exp_pos 1).le (sq_nonneg v)]

private theorem perturbed_tail_upper {ε δ v : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hv : splitMultiplier * δ ≤ v)
    (hδsmall : δ ≤ 1 / (8 * Real.exp 1))
    (hexpsmall : Real.exp (ε * δ) ≤ 2) :
    errorNumerator ε δ v ≤ -(ε / 2) * v := by
  have hm : 0 < splitMultiplier := by unfold splitMultiplier; positivity
  have hv0 : 0 ≤ v := (mul_pos hm hδ).le.trans hv
  have hh := concentratedLog_bounds hε hδ hv0
  have he : Real.exp (concentratedLog ε δ v) ≤ 2 :=
    (Real.exp_le_exp.mpr hh.2.1).trans hexpsmall
  have he1 : Real.exp (concentratedLog ε δ v) - 1 ≤
      concentratedLog ε δ v * Real.exp (concentratedLog ε δ v) := by
    have htan := mul_le_mul_of_nonneg_right
      (Real.add_one_le_exp (-concentratedLog ε δ v))
      (Real.exp_pos (concentratedLog ε δ v)).le
    rw [← Real.exp_add] at htan
    simp only [neg_add_cancel, Real.exp_zero] at htan
    nlinarith
  have hE : Real.exp (concentratedLog ε δ v) - 1 ≤ 2 * ε * δ := by
    have hm := mul_le_mul hh.2.1 he (Real.exp_pos _).le (mul_nonneg hε hδ.le)
    nlinarith
  have hφ := actualPhi_linear_envelope hv0
  have hφ0 := (actualPhi_pos v).le
  have hA := mul_le_mul_of_nonneg_left hE hφ0
  have hA' := mul_le_mul_of_nonneg_right hφ (by positivity : 0 ≤ 2 * ε * δ)
  have hδpay : 8 * Real.exp 1 * δ ≤ 1 := by
    have h := (le_div_iff₀ (show (0 : ℝ) < 8 * Real.exp 1 by positivity)).mp hδsmall
    nlinarith
  have hloc : 8 * Real.exp 1 * δ ≤ v := by simpa [splitMultiplier] using hv
  rw [errorNumerator_eq]
  have hpay1 := mul_le_mul_of_nonneg_right hδpay hv0
  have hpay2 := mul_le_mul_of_nonneg_left hloc hε
  have hpay3 := mul_le_mul_of_nonneg_left hpay1 hε
  nlinarith


private def secondBudget (ε δ : ℝ) : ℝ :=
  Real.exp 1 * (Real.exp (ε * δ) * ((1 + ε) ^ 2 + 1 / 2 + ε / δ) + 3 / 2)

private theorem error_second_bound {ε δ v : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hv : 0 ≤ v) :
    |perturbedRatio ε δ v *
        (concentratedSlope ε δ v ^ 2 - profileCurvature v -
          (ε / δ) * Real.exp (-v / δ)) -
      actualPhi v * (rate v ^ 2 - profileCurvature v)| ≤
        secondBudget ε δ * (1 + v) := by
  have hr := rate_bounds hv
  have hj := profileCurvature_bounds hv
  have he : Real.exp (-v / δ) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
  have hS0 : 0 ≤ concentratedSlope ε δ v :=
    (perturbed_first_order hε hδ hv).2.2.2.2
  have hS1 : concentratedSlope ε δ v ≤ 1 + ε := by
    unfold concentratedSlope
    have hm := mul_le_mul_of_nonneg_left he hε
    linarith
  have hSsq : concentratedSlope ε δ v ^ 2 ≤ (1 + ε) ^ 2 :=
    (sq_le_sq₀ hS0 (by positivity)).2 hS1
  have hrsq : rate v ^ 2 ≤ 1 := by nlinarith
  have hcor0 : 0 ≤ (ε / δ) * Real.exp (-v / δ) :=
    mul_nonneg (div_nonneg hε hδ.le) (Real.exp_pos _).le
  have hcor1 : (ε / δ) * Real.exp (-v / δ) ≤ ε / δ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (div_nonneg hε hδ.le)
  have hc1 : |concentratedSlope ε δ v ^ 2 - profileCurvature v -
      (ε / δ) * Real.exp (-v / δ)| ≤ (1 + ε) ^ 2 + 1 / 2 + ε / δ := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (concentratedSlope ε δ v)]
  have hc0 : |rate v ^ 2 - profileCurvature v| ≤ 3 / 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (rate v)]
  have hP0 := (actualPhi_pos v).le
  have hF0 : 0 ≤ perturbedRatio ε δ v :=
    (mul_pos (actualPhi_pos v) (Real.exp_pos (concentratedLog ε δ v))).le
  have hP := actualPhi_linear_envelope hv
  have hlog := (concentratedLog_bounds hε hδ hv).2.1
  have hF : perturbedRatio ε δ v ≤ Real.exp 1 * (1 + v) * Real.exp (ε * δ) := by
    unfold perturbedRatio
    exact mul_le_mul hP (Real.exp_le_exp.mpr hlog) (Real.exp_pos _).le (by positivity)
  calc
    _ ≤ |perturbedRatio ε δ v *
          (concentratedSlope ε δ v ^ 2 - profileCurvature v -
            (ε / δ) * Real.exp (-v / δ))| +
        |actualPhi v * (rate v ^ 2 - profileCurvature v)| := abs_sub _ _
    _ ≤ (Real.exp 1 * (1 + v) * Real.exp (ε * δ)) *
          ((1 + ε) ^ 2 + 1 / 2 + ε / δ) + (Real.exp 1 * (1 + v)) * (3 / 2) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hF0, abs_of_nonneg hP0]
      exact add_le_add (mul_le_mul hF hc1 (abs_nonneg _) (by positivity))
        (mul_le_mul hP hc0 (abs_nonneg _) (by positivity))
    _ = _ := by unfold secondBudget; ring

private theorem error_quadratic_global {ε δ v : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hv : 0 ≤ v) :
    |errorNumerator ε δ v| ≤ secondBudget ε δ * (1 + v) * v ^ 2 / 2 := by
  let g : ℝ → ℝ := fun w =>
    perturbedRatio ε δ w * concentratedSlope ε δ w - actualPhi w * rate w - ε
  let h : ℝ → ℝ := fun w =>
    perturbedRatio ε δ w *
      (concentratedSlope ε δ w ^ 2 - profileCurvature w -
        (ε / δ) * Real.exp (-w / δ)) -
      actualPhi w * (rate w ^ 2 - profileCurvature w)
  have hC : 0 ≤ secondBudget ε δ := by unfold secondBudget; positivity
  have hg0 : g 0 = 0 := by
    dsimp [g]
    rw [perturbedRatio_zero, concentratedSlope_zero, actualPhi_zero, rate_zero]
    ring
  apply exact_zero_quadratic_bound (errorNumerator ε δ) g h hv
    (errorNumerator_zero ε δ) hg0
    (fun w hw => hasDerivAt_errorNumerator hδ.ne')
    (fun w hw => error_second_derivative hδ.ne')
  intro w hw
  rw [Real.norm_eq_abs]
  exact (error_second_bound hε hδ hw.1).trans
    (mul_le_mul_of_nonneg_left (by linarith [hw.2]) hC)

private theorem original_quadratic_global {v : ℝ} (hv : 0 ≤ v) :
    |originalNumerator v| ≤ ((3 / 2) * Real.exp 1) * (1 + v) * v ^ 2 / 2 := by
  let g : ℝ → ℝ := fun w => actualPhi w * rate w - 1
  let h : ℝ → ℝ := fun w => actualPhi w * (rate w ^ 2 - profileCurvature w)
  have hf (w : ℝ) : HasDerivAt originalNumerator (g w) w := by
    have hd := ((hasDerivAt_actualPhi w).sub_const 1).sub (hasDerivAt_id w)
    have hh := hd.congr_deriv (show actualPhi w * rate w - 1 = g w by rfl)
    apply hh.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun u => rfl)
  have hg (w : ℝ) : HasDerivAt g (h w) w := by
    have hd := ((hasDerivAt_actualPhi w).mul (hasDerivAt_rate w)).sub_const 1
    apply hd.congr_deriv
    ring
  have hf0 : originalNumerator 0 = 0 := by simp [originalNumerator, actualPhi_zero]
  have hg0 : g 0 = 0 := by simp [g, actualPhi_zero, rate_zero]
  apply exact_zero_quadratic_bound originalNumerator g h hv hf0 hg0
    (fun w hw => hf w) (fun w hw => hg w)
  intro w hw
  have hr := rate_bounds hw.1
  have hj := profileCurvature_bounds hw.1
  have hco : |rate w ^ 2 - profileCurvature w| ≤ 3 / 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (rate w)]
  have hP : actualPhi w ≤ Real.exp 1 * (1 + v) :=
    (actualPhi_linear_envelope hw.1).trans
      (mul_le_mul_of_nonneg_left (by linarith [hw.2]) (Real.exp_pos 1).le)
  dsimp [h]
  rw [abs_mul, abs_of_pos (actualPhi_pos w)]
  have hb := mul_le_mul hP hco (abs_nonneg _) (by positivity)
  calc
    _ ≤ (Real.exp 1 * (1 + v)) * (3 / 2) := hb
    _ = _ := by ring

private theorem signed_integrable_of_quadratic (f : ℝ → ℝ) {σ C : ℝ}
    (hσ : 0 < σ) (hf : ContinuousOn f (Ioi 0))
    (hbound : ∀ v : ℝ, 0 ≤ v → |f v| ≤ C * (1 + v) * v ^ 2 / 2) :
    IntegrableOn (fun v : ℝ => Real.exp (-σ * v) * f v / v ^ 2) (Ioi 0) := by
  have h0 := exp_moment_integrable hσ 0
  have h1 := exp_moment_integrable hσ 1
  have hmajor : IntegrableOn (fun v : ℝ =>
      (C / 2) * (1 + v) * Real.exp (-σ * v)) (Ioi 0) := by
    apply IntegrableOn.congr_fun ((h0.add h1).const_mul (C / 2)) _ measurableSet_Ioi
    intro v hv
    simp only [Pi.add_apply, pow_zero, one_mul, pow_one]
    ring
  have hmeas : ContinuousOn (fun v : ℝ =>
      Real.exp (-σ * v) * f v / v ^ 2) (Ioi 0) := by
    intro v hv
    have hE : ContinuousWithinAt (fun w : ℝ => Real.exp (-σ * w)) (Ioi 0) v :=
      (show ContinuousAt (fun w : ℝ => Real.exp (-σ * w)) v by fun_prop).continuousWithinAt
    exact (hE.mul (hf v hv)).div (continuousWithinAt_id.pow 2) (pow_ne_zero 2 (mem_Ioi.mp hv).ne')
  apply hmajor.mono' (hmeas.aestronglyMeasurable measurableSet_Ioi)
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro v hv
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (sq_nonneg v)]
  calc
    _ ≤ Real.exp (-σ * v) * (C * (1 + v) * v ^ 2 / 2) / v ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbound v hv.le) (Real.exp_pos _).le) (sq_nonneg v)
    _ = (C / 2) * (1 + v) * Real.exp (-σ * v) := by field_simp [(mem_Ioi.mp hv).ne'] <;> ring

private theorem original_integrand_integrable {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun v : ℝ => Real.exp (-σ * v) * originalNumerator v / v ^ 2) (Ioi 0) :=
  signed_integrable_of_quadratic originalNumerator hσ
    (fun v hv => (((hasDerivAt_actualPhi v).sub_const 1).sub
      (hasDerivAt_id v)).continuousAt.continuousWithinAt)
    (fun v hv => original_quadratic_global hv)

private theorem error_integrand_integrable {ε δ σ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hσ : 0 < σ) :
    IntegrableOn (errorIntegrand ε δ σ) (Ioi 0) :=
  signed_integrable_of_quadratic (errorNumerator ε δ) hσ
    (fun v hv => (hasDerivAt_errorNumerator hδ.ne').continuousAt.continuousWithinAt)
    (fun v hv => error_quadratic_global hε hδ hv)

private theorem perturbed_integrand_integrable {ε δ σ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hσ : 0 < σ) :
    IntegrableOn (fun v : ℝ => Real.exp (-σ * v) * perturbedNumerator ε δ v / v ^ 2)
      (Ioi 0) := by
  have h := (error_integrand_integrable hε hδ hσ).add (original_integrand_integrable hσ)
  apply h.congr_fun _ measurableSet_Ioi
  intro v hv
  simp only [Pi.add_apply]
  unfold errorIntegrand errorNumerator
  ring

private theorem signed_integral_difference {ε δ σ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hσ : 0 < σ) :
    (∫ v in Ioi (0 : ℝ), Real.exp (-σ * v) * perturbedNumerator ε δ v / v ^ 2) -
      (∫ v in Ioi (0 : ℝ), Real.exp (-σ * v) * originalNumerator v / v ^ 2) =
        errorIntegral ε δ σ := by
  rw [← integral_sub (perturbed_integrand_integrable hε hδ hσ)
    (original_integrand_integrable hσ)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  simp only [Pi.add_apply]
  unfold errorIntegrand errorNumerator
  ring


private theorem errorIntegral_upper {ε δ σ : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hσ : 0 < σ)
    (hδsmall : δ ≤ 1 / (8 * Real.exp 1))
    (hexpsmall : Real.exp (ε * δ) ≤ 2) :
    errorIntegral ε δ σ ≤ 2 * Real.exp 1 * splitMultiplier * ε * δ -
      (ε * Real.exp (-σ) / 2) * Real.log (1 / (splitMultiplier * δ)) := by
  let t : ℝ := splitMultiplier * δ
  let c : ℝ := ε * Real.exp (-σ) / 2
  have hm : 0 < splitMultiplier := by unfold splitMultiplier; positivity
  have ht : 0 < t := mul_pos hm hδ
  have ht1 : t ≤ 1 := by
    dsimp [t, splitMultiplier]
    have h := (le_div_iff₀ (show (0 : ℝ) < 8 * Real.exp 1 by positivity)).mp hδsmall
    nlinarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hf := error_integrand_integrable hε hδ hσ
  have hft : IntegrableOn (errorIntegrand ε δ σ) (Ioi t) :=
    hf.mono_set (Ioi_subset_Ioi ht.le)
  have hf1 : IntegrableOn (errorIntegrand ε δ σ) (Ioi 1) :=
    hf.mono_set (Ioi_subset_Ioi zero_le_one)
  have hnearI : IntervalIntegrable (errorIntegrand ε δ σ) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr
      (hf.mono_set Ioc_subset_Ioi_self)
  have hmiddleI : IntervalIntegrable (errorIntegrand ε δ σ) volume t 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht1).mpr
      (hf.mono_set (fun v hv => ht.trans hv.1))
  have hnear : (∫ v in (0 : ℝ)..t, errorIntegrand ε δ σ v) ≤
      2 * Real.exp 1 * ε * t := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo ht.le hnearI
      (intervalIntegrable_const :
        IntervalIntegrable (fun _ : ℝ => 2 * Real.exp 1 * ε) volume 0 t) (fun v hv => by
        have hv0 : 0 < v := hv.1
        have hloc := perturbed_local_upper hε hε1 hδ hv0.le (hv.2.le.trans ht1)
        have he : Real.exp (-σ * v) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith)
        have hA := mul_le_mul_of_nonneg_left hloc (Real.exp_pos (-σ * v)).le
        have hB := mul_le_mul_of_nonneg_right he
          (by positivity : 0 ≤ 2 * Real.exp 1 * ε * v ^ 2)
        unfold errorIntegrand
        calc
          _ ≤ (2 * Real.exp 1 * ε * v ^ 2) / v ^ 2 :=
            div_le_div_of_nonneg_right (hA.trans (by simpa using hB)) (sq_nonneg v)
          _ = 2 * Real.exp 1 * ε := by field_simp [hv0.ne'])
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using h
  have hg : IntervalIntegrable (fun v : ℝ => -c * (1 / v)) volume t 1 := by
    apply (ContinuousOn.const_mul _ (-c)).intervalIntegrable_of_Icc ht1
    exact continuousOn_const.div continuousOn_id
      (fun v hv => (ht.trans_le hv.1).ne')
  have hmiddle : (∫ v in t..1, errorIntegrand ε δ σ v) ≤
      -c * Real.log (1 / t) := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo ht1 hmiddleI hg (fun v hv => by
      have hv0 : 0 < v := ht.trans hv.1
      have htail := perturbed_tail_upper hε hδ hv.1.le hδsmall hexpsmall
      have he : Real.exp (-σ) ≤ Real.exp (-σ * v) :=
        Real.exp_le_exp.mpr (by nlinarith [hv.2])
      have hm := mul_le_mul_of_nonpos_left he (by linarith : -(ε / 2) ≤ 0)
      unfold errorIntegrand
      calc
        _ ≤ Real.exp (-σ * v) * (-(ε / 2) * v) / v ^ 2 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le) (sq_nonneg v)
        _ = (-(ε / 2) * Real.exp (-σ * v)) / v := by field_simp [hv0.ne'] <;> ring
        _ ≤ (-(ε / 2) * Real.exp (-σ)) / v :=
          div_le_div_of_nonneg_right hm hv0.le
        _ = -c * (1 / v) := by dsimp [c]; ring)
    simpa only [intervalIntegral.integral_const_mul,
      integral_one_div_of_pos ht (by norm_num : (0 : ℝ) < 1)] using h
  have htail : (∫ v in Ioi (1 : ℝ), errorIntegrand ε δ σ v) ≤ 0 := by
    apply integral_nonpos_of_ae
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro v hv
    have hv1 : 1 < v := mem_Ioi.mp hv
    have hnum := perturbed_tail_upper hε hδ (ht1.trans hv.le) hδsmall hexpsmall
    have hnum0 : errorNumerator ε δ v ≤ 0 :=
      hnum.trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hv1]))
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hnum0) (sq_nonneg v)
  have hs0 := intervalIntegral.integral_interval_add_Ioi hf hft
  have hs1 := intervalIntegral.integral_interval_add_Ioi hft hf1
  unfold errorIntegral
  dsimp [t, c] at hnear hmiddle hs0 hs1
  nlinarith

private theorem concentrationScale_pos (ε : ℝ) : 0 < concentrationScale ε :=
  Real.exp_pos _

private theorem concentrationScale_tendsto :
    Tendsto concentrationScale (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hi : Tendsto (fun ε : ℝ => ε⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hp := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hi
  have hn := tendsto_neg_atTop_atBot.comp hp
  have he := Real.tendsto_exp_atBot.comp hn
  change Tendsto (fun ε : ℝ => Real.exp (-((ε⁻¹) ^ 2))) (𝓝[>] (0 : ℝ)) (𝓝 0) at he
  have heq : (fun ε : ℝ => Real.exp (-((ε⁻¹) ^ 2))) = concentrationScale := by
    funext ε
    simp only [concentrationScale, neg_div, one_div, inv_pow]
  rw [heq] at he
  exact he

private theorem concentrationScale_eventually_small :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 < ε ∧ ε ≤ 1 ∧ concentrationScale ε ≤ 1 ∧
      concentrationScale ε ≤ 1 / (8 * Real.exp 1) ∧
      Real.exp (ε * concentrationScale ε) ≤ 2 := by
  have hz : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have he : Tendsto (fun ε : ℝ => Real.exp (ε * concentrationScale ε))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [Function.comp_def, zero_mul, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp (hz.mul concentrationScale_tendsto)
  filter_upwards [self_mem_nhdsWithin,
    hz.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    concentrationScale_tendsto.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    concentrationScale_tendsto.eventually (Iio_mem_nhds
      (by positivity : (0 : ℝ) < 1 / (8 * Real.exp 1))),
    he.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))] with ε hε hε1 hδ1 hδ hE
  exact ⟨hε, hε1.le, hδ1.le, hδ.le, hE.le⟩

private theorem errorIntegral_scaled_upper {ε σ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ1 : concentrationScale ε ≤ 1)
    (hδ : concentrationScale ε ≤ 1 / (8 * Real.exp 1))
    (hE : Real.exp (ε * concentrationScale ε) ≤ 2) (hσ : 0 < σ) :
    errorIntegral ε (concentrationScale ε) σ ≤
      2 * Real.exp 1 * splitMultiplier +
        (Real.exp (-σ) / 2) * |Real.log splitMultiplier| -
          (Real.exp (-σ) / 2) / ε := by
  have hm : 0 < splitMultiplier := by unfold splitMultiplier; positivity
  have hs := concentrationScale_pos ε
  have hu := errorIntegral_upper hε.le hε1 hs hσ hδ hE
  have hl : Real.log (1 / (splitMultiplier * concentrationScale ε)) =
      1 / ε ^ 2 - Real.log splitMultiplier := by
    rw [Real.log_div one_ne_zero (mul_ne_zero hm.ne' hs.ne'), Real.log_one,
      Real.log_mul hm.ne' hs.ne']
    unfold concentrationScale
    rw [Real.log_exp]
    ring
  rw [hl] at hu
  have hb : ε * concentrationScale ε ≤ 1 := by
    exact (mul_le_mul hε1 hδ1 hs.le (by norm_num : (0 : ℝ) ≤ 1)).trans (by norm_num)
  have hA := mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ 2 * Real.exp 1 * splitMultiplier)
  have hlog : ε * Real.log splitMultiplier ≤ |Real.log splitMultiplier| := by
    calc
      _ ≤ ε * |Real.log splitMultiplier| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
      _ ≤ |Real.log splitMultiplier| := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hε1 (abs_nonneg _)
  have hB := mul_le_mul_of_nonneg_left hlog
    (by positivity : 0 ≤ Real.exp (-σ) / 2)
  have heq : (ε * Real.exp (-σ) / 2) * (1 / ε ^ 2 - Real.log splitMultiplier) =
      (Real.exp (-σ) / 2) / ε - (Real.exp (-σ) / 2) * (ε * Real.log splitMultiplier) := by
    field_simp [hε.ne'] <;> ring
  rw [heq] at hu
  nlinarith

private theorem errorIntegral_tendsto_atBot {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun ε : ℝ => errorIntegral ε (concentrationScale ε) σ)
      (𝓝[>] (0 : ℝ)) atBot := by
  let C : ℝ := 2 * Real.exp 1 * splitMultiplier +
    (Real.exp (-σ) / 2) * |Real.log splitMultiplier|
  let c : ℝ := Real.exp (-σ) / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hi : Tendsto (fun ε : ℝ => ε⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  apply tendsto_atBot.2
  intro b
  filter_upwards [concentrationScale_eventually_small,
    hi.eventually_ge_atTop ((C - b) / c)] with ε hsmall hinv
  rcases hsmall with ⟨hε, hε1, hδ1, hδ, hE⟩
  have hu := errorIntegral_scaled_upper hε hε1 hδ1 hδ hE hσ
  have hp := mul_le_mul_of_nonneg_left hinv hc.le
  have hbc : C - b ≤ c * ε⁻¹ := by
    simpa only [mul_div_cancel₀ _ hc.ne'] using hp
  change errorIntegral ε (concentrationScale ε) σ ≤ b
  change errorIntegral ε (concentrationScale ε) σ ≤ C - c / ε at hu
  rw [div_eq_mul_inv] at hu
  linarith

private theorem perturbedSlope_strictAnti {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    StrictAnti (concentratedSlope ε δ) := by
  apply strictAnti_of_hasDerivAt_neg (fun v => hasDerivAt_concentratedSlope (ε := ε) (v := v) hδ.ne')
  intro v
  change -profileCurvature v - (ε / δ) * Real.exp (-v / δ) < (0 : ℝ)
  have hj := profileCurvature_nonneg v
  have hx := mul_pos (div_pos hε hδ) (Real.exp_pos (-v / δ))
  linarith

/-- Original-Phi information insufficiency: all-axis first-order bounds coexist
with a negative logarithmic concentration block and divergent exact compensation.
This constructed family is not an assertion about an actual prime Euler family. -/
theorem result :
    (∀ ε : ℝ, 0 < ε →
      perturbedRatio ε (concentrationScale ε) 0 = 1 ∧
      concentratedSlope ε (concentrationScale ε) 0 = 1 + ε ∧
      Antitone (concentratedSlope ε (concentrationScale ε)) ∧
      StrictAnti (concentratedSlope ε (concentrationScale ε)) ∧
      (∀ v : ℝ, HasDerivAt (perturbedRatio ε (concentrationScale ε))
        (perturbedRatio ε (concentrationScale ε) v *
          concentratedSlope ε (concentrationScale ε) v) v) ∧
      (∀ v : ℝ, 0 ≤ v →
        0 < perturbedRatio ε (concentrationScale ε) v ∧
        Real.exp (-ε * v) * actualPhi v ≤ perturbedRatio ε (concentrationScale ε) v ∧
        perturbedRatio ε (concentrationScale ε) v ≤ Real.exp (ε * v) * actualPhi v ∧
        |concentratedSlope ε (concentrationScale ε) v - rate v| ≤ ε ∧
        0 < concentratedSlope ε (concentrationScale ε) v) ∧
      errorNumerator ε (concentrationScale ε) 0 = 0 ∧
      HasDerivAt (errorNumerator ε (concentrationScale ε)) 0 0 ∧
      (∀ v : ℝ, errorNumerator ε (concentrationScale ε) v =
        actualPhi v * (Real.exp (concentratedLog ε (concentrationScale ε) v) - 1) - ε * v) ∧
      (∀ σ : ℝ, 0 < σ →
        IntegrableOn (fun v : ℝ =>
          Real.exp (-σ * v) * originalNumerator v / v ^ 2) (Ioi 0) ∧
        IntegrableOn (fun v : ℝ =>
          Real.exp (-σ * v) * perturbedNumerator ε (concentrationScale ε) v / v ^ 2)
          (Ioi 0) ∧
        IntegrableOn (errorIntegrand ε (concentrationScale ε) σ) (Ioi 0) ∧
        (∫ v in Ioi (0 : ℝ),
          Real.exp (-σ * v) * perturbedNumerator ε (concentrationScale ε) v / v ^ 2) -
        (∫ v in Ioi (0 : ℝ), Real.exp (-σ * v) * originalNumerator v / v ^ 2) =
          errorIntegral ε (concentrationScale ε) σ)) ∧
    (∀ σ : ℝ, 0 < σ →
      Tendsto (fun ε : ℝ => errorIntegral ε (concentrationScale ε) σ)
        (𝓝[>] (0 : ℝ)) atBot) := by
  constructor
  · intro ε hε
    have hδ := concentrationScale_pos ε
    refine ⟨perturbedRatio_zero ε _, concentratedSlope_zero ε _,
      perturbedSlope_antitone hε.le hδ, perturbedSlope_strictAnti hε hδ,
      (fun v => hasDerivAt_perturbedRatio (ε := ε) (v := v) hδ.ne'), ?_,
      errorNumerator_zero ε _, hasDerivAt_errorNumerator_zero hδ.ne',
      (fun v => errorNumerator_eq ε _ v), ?_⟩
    · intro v hv
      have h := perturbed_first_order hε.le hδ hv
      refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
      unfold concentratedSlope
      exact add_pos_of_nonneg_of_pos (rate_nonneg v) (mul_pos hε (Real.exp_pos _))
    · intro σ hσ
      exact ⟨original_integrand_integrable hσ,
        perturbed_integrand_integrable hε.le hδ hσ,
        error_integrand_integrable hε.le hδ hσ,
        signed_integral_difference hε.le hδ hσ⟩
  · intro σ hσ
    exact errorIntegral_tendsto_atBot hσ

end D5.S3.Arith.Robin.PrimorialFirstOrderConcentrationCounterexample

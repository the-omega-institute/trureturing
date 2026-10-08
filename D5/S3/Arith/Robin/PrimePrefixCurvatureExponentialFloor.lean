/- GID: D5/S3/Arith/Robin/PrimePrefixCurvatureExponentialFloor
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PrimePrefixCurvatureExponentialFloor
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The literal curvature times exp is strictly increasing from one half and has a strict whole-axis exponential floor. -/

import D5.S3.Arith.Robin.PrimePrefixPhiCurvature
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
The literal Phi and its first derivative are supplied by
PrimorialGlobalLaplaceEnvelope. The all-real rate differentiation,
literal second-derivative binding, and closed curvature expression below
are consumed copies of the existing private proof chain in
PrimePrefixPhiCurvature. That dominated compact-input derivative retains
the PrimorialFirstOrderConcentrationCounterexample provenance.

The new exponential-polynomial sign chain proves that exp(v)*Phi''(v)
strictly increases on the entire nonnegative axis from its literal zero
value 1/2. The resulting positive remainder is the exact density used
by the original A exponential-floor bound. No Robin signed tail or RH
acceptance is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter MeasureTheory
open scoped Topology Interval
open D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope

namespace D5.S3.Arith.Robin.PrimePrefixCurvatureExponentialFloor

private def rateMoment (v : ℝ) : ℝ :=
  ∫ b in (0 : ℝ)..1, b * Real.exp (-v * b)

private def B (v : ℝ) : ℝ :=
  actualPhi v * (rate v ^ 2 - rateMoment v)

private theorem continuous_rate : Continuous rate := by
  unfold rate
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop) 0 1

private theorem continuous_rateMoment : Continuous rateMoment := by
  unfold rateMoment
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop) 0 1

private theorem continuous_actualPhi : Continuous actualPhi :=
  continuous_iff_continuousAt.mpr
    (fun v => (hasDerivAt_actualPhi v).continuousAt)

private theorem continuous_B : Continuous B := by
  unfold B
  exact continuous_actualPhi.mul
    ((continuous_rate.pow 2).sub continuous_rateMoment)

private theorem rate_zero : rate 0 = 1 := by
  simp [rate]

private theorem rateMoment_zero : rateMoment 0 = 1 / 2 := by
  norm_num [rateMoment, integral_id]

private theorem B_zero : B 0 = 1 / 2 := by
  rw [B, actualPhi_zero, rate_zero, rateMoment_zero]
  norm_num

/-- Original all-real rate differentiation, including its zero endpoint. -/
private theorem hasDerivAt_rate (v : ℝ) :
    HasDerivAt rate (-rateMoment v) v := by
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


private theorem hasDerivAt_phi_slope (v : ℝ) :
    HasDerivAt (fun w : ℝ => actualPhi w * rate w) (B v) v := by
  have h := (hasDerivAt_actualPhi v).mul (hasDerivAt_rate v)
  apply h.congr_deriv
  unfold B
  ring

private theorem actualPhi_second_derivative (v : ℝ) :
    deriv (deriv actualPhi) v = B v := by
  have hfun : deriv actualPhi = fun w : ℝ => actualPhi w * rate w := by
    funext w
    exact (hasDerivAt_actualPhi w).deriv
  rw [hfun]
  exact (hasDerivAt_phi_slope v).deriv

/-- Reuse of the original envelope's finite-integral rate computation. -/
private theorem rate_eq {v : ℝ} (hv : v ≠ 0) :
    rate v = (1 - Real.exp (-v)) / v := by
  unfold rate
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hv)]
  simp only [mul_zero, mul_one, integral_exp, Real.exp_zero, smul_eq_mul]
  field_simp
  ring

private theorem hasDerivAt_rate_closed {v : ℝ} (hv : 0 < v) :
    HasDerivAt rate (((v + 1) * Real.exp (-v) - 1) / v ^ 2) v := by
  have hclosed : HasDerivAt
      (fun w : ℝ => (1 - Real.exp (-w)) / w)
      (((v + 1) * Real.exp (-v) - 1) / v ^ 2) v := by
    have h := ((hasDerivAt_const v (1 : ℝ)).sub
      ((hasDerivAt_id v).neg.exp)).div (hasDerivAt_id v) hv.ne'
    apply h.congr_deriv
    dsimp
    ring
  apply hclosed.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hv] with w hw
  exact rate_eq (show w ≠ 0 from (show 0 < w from hw).ne')

private theorem rateMoment_eq {v : ℝ} (hv : 0 < v) :
    rateMoment v = (1 - (1 + v) * Real.exp (-v)) / v ^ 2 := by
  have h := (hasDerivAt_rate v).unique (hasDerivAt_rate_closed hv)
  calc
    rateMoment v = -(((v + 1) * Real.exp (-v) - 1) / v ^ 2) := by
      linarith
    _ = (1 - (1 + v) * Real.exp (-v)) / v ^ 2 := by ring

private theorem B_closed {v : ℝ} (hv : 0 < v) :
    B v = actualPhi v * Real.exp (-v) *
      (v - 1 + Real.exp (-v)) / v ^ 2 := by
  unfold B
  rw [rate_eq hv.ne', rateMoment_eq hv]
  field_simp [hv.ne']
  <;> ring


/-- The literal curvature after the fixed unit-rate exponential floor. -/
def curvatureRemainder (v : ℝ) : ℝ :=
  deriv (deriv actualPhi) v - Real.exp (-v)/2

private def tiltedB (v : ℝ) : ℝ := Real.exp v * B v

private def exponentialGap (v : ℝ) : ℝ :=
  Real.exp v - Real.exp (-v) - 2*v

private theorem hasDerivAt_exponentialGap (v : ℝ) :
    HasDerivAt exponentialGap (Real.exp v+Real.exp (-v)-2) v := by
  have h := ((Real.hasDerivAt_exp v).sub ((hasDerivAt_id v).neg.exp)).sub
    ((hasDerivAt_id v).const_mul 2)
  apply h.congr_deriv
  dsimp
  ring

private theorem exponentialGap_derivative_pos {v : ℝ} (hv : 0 < v) :
    0 < Real.exp v+Real.exp (-v)-2 := by
  have he : 1 < Real.exp v := by simpa using Real.exp_lt_exp.mpr hv
  have hformula : Real.exp v+Real.exp (-v)-2 =
      (Real.exp v-1)^2/Real.exp v := by
    rw [Real.exp_neg]
    field_simp
    ring
  rw [hformula]
  exact div_pos (pow_pos (sub_pos.mpr he) 2) (Real.exp_pos v)

private theorem exponentialGap_strictMono :
    StrictMonoOn exponentialGap (Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
    (show ContinuousOn exponentialGap (Ici (0 : ℝ)) from
      (show Continuous exponentialGap by unfold exponentialGap; fun_prop).continuousOn)
  intro v hv
  have hv0 : 0 < v := by simpa only [interior_Ici, mem_Ioi] using hv
  rw [(hasDerivAt_exponentialGap v).deriv]
  exact exponentialGap_derivative_pos hv0

private theorem exponentialGap_pos {v : ℝ} (hv : 0 < v) :
    0 < exponentialGap v := by
  have h := exponentialGap_strictMono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hv.le) hv
  simpa [exponentialGap] using h

private theorem tiltedB_closed {v : ℝ} (hv : 0 < v) :
    tiltedB v = actualPhi v*(v-1+Real.exp (-v))/v^2 := by
  unfold tiltedB
  rw [B_closed hv]
  have he : Real.exp v*Real.exp (-v) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    Real.exp v*(actualPhi v*Real.exp (-v)*(v-1+Real.exp (-v))/v^2)
        = (Real.exp v*Real.exp (-v))*
          (actualPhi v*(v-1+Real.exp (-v)))/v^2 := by ring
    _ = actualPhi v*(v-1+Real.exp (-v))/v^2 := by rw [he]; ring

private theorem hasDerivAt_tiltedB {v : ℝ} (hv : 0 < v) :
    HasDerivAt tiltedB
      (actualPhi v*(1-2*v*Real.exp (-v)-Real.exp (-v)^2)/v^3) v := by
  have hclosed : HasDerivAt
      (fun w : ℝ => actualPhi w*(w-1+Real.exp (-w))/w^2)
      (actualPhi v*(1-2*v*Real.exp (-v)-Real.exp (-v)^2)/v^3) v := by
    have hnum := (hasDerivAt_actualPhi v).mul
      (((hasDerivAt_id v).sub_const 1).add ((hasDerivAt_id v).neg.exp))
    have h := hnum.div ((hasDerivAt_id v).pow 2) (pow_ne_zero 2 hv.ne')
    apply h.congr_deriv
    dsimp
    rw [rate_eq hv.ne']
    field_simp [hv.ne']
    <;> ring
  apply hclosed.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hv] with w hw
  exact tiltedB_closed (show 0 < w from hw)

private theorem tiltedB_derivative_pos {v : ℝ} (hv : 0 < v) :
    0 < deriv tiltedB v := by
  have he : Real.exp (-v)*Real.exp v = 1 := by
    rw [← Real.exp_add]
    simp
  have hid : 1-2*v*Real.exp (-v)-Real.exp (-v)^2 =
      Real.exp (-v)*exponentialGap v := by
    unfold exponentialGap
    nlinarith [he]
  rw [(hasDerivAt_tiltedB hv).deriv, hid]
  exact div_pos
    (mul_pos (actualPhi_pos v) (mul_pos (Real.exp_pos (-v)) (exponentialGap_pos hv)))
    (pow_pos hv 3)

private theorem tiltedB_strictMono : StrictMonoOn tiltedB (Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
    ((Real.continuous_exp.mul continuous_B).continuousOn)
  intro v hv
  exact tiltedB_derivative_pos (by simpa only [interior_Ici, mem_Ioi] using hv)

private theorem floor_lt {v : ℝ} (hv : 0 < v) :
    Real.exp (-v)/2 < deriv (deriv actualPhi) v := by
  have h := tiltedB_strictMono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hv.le) hv
  have hz : tiltedB 0 = (1/2 : ℝ) := by simp [tiltedB, B_zero]
  rw [hz] at h
  unfold tiltedB at h
  have hm := mul_lt_mul_of_pos_left h (Real.exp_pos (-v))
  have he : Real.exp (-v)*Real.exp v = 1 := by
    rw [← Real.exp_add]
    simp
  rw [actualPhi_second_derivative]
  rw [← mul_assoc, he, one_mul] at hm
  simpa only [div_eq_mul_inv, one_mul] using hm

/-- Exact positive remainder for the same literal actual Phi on the whole positive axis. -/
theorem result :
    StrictMonoOn (fun v : ℝ => Real.exp v*deriv (deriv actualPhi) v)
      (Ici (0 : ℝ)) ∧
    (∀ v : ℝ, 0 < v →
      Real.exp (-v)/2 < deriv (deriv actualPhi) v ∧
      0 < curvatureRemainder v) ∧
    curvatureRemainder 0 = 0 := by
  have hfun : (fun v : ℝ => Real.exp v*deriv (deriv actualPhi) v) = tiltedB := by
    funext v
    rw [actualPhi_second_derivative]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact tiltedB_strictMono
  · intro v hv
    have hf := floor_lt hv
    exact ⟨hf, sub_pos.mpr hf⟩
  · simp [curvatureRemainder, actualPhi_second_derivative, B_zero]

end D5.S3.Arith.Robin.PrimePrefixCurvatureExponentialFloor

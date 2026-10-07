/- GID: D5/S3/Arith/Robin/PrimePrefixPhiCurvature
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PrimePrefixPhiCurvature
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: A fourth derivative sign chain proves positive and strictly decreasing curvature for the literal prime-prefix Phi. -/

import D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
The literal prime-prefix Phi and rate are supplied by
D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope, together with the original
first derivative, zero value, and positivity.

The complete dominated proof of `hasDerivAt_rate` is reused from the private
helper in PrimorialFirstOrderConcentrationCounterexample.lean:84-153; only
its local moment name changes to `rateMoment`. This moment is -rate' and
computes the actual second derivative through Phi*(rate^2-rateMoment).

The D/T exponential-polynomial sign chain is the repository derivation in
actual-prefix theory section 444.1. Its fourth derivative is positive on
Ici 0. Successive strict monotonicity gives D<0 throughout the positive axis,
which makes the actual Phi curvature strictly decrease, including the zero
endpoint through the original integral model's continuity.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter MeasureTheory
open scoped Topology Interval
open D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope

namespace D5.S3.Arith.Robin.PrimePrefixPhiCurvature

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

private theorem exp_remainder_pos {v : ℝ} (hv : 0 < v) :
    0 < v - 1 + Real.exp (-v) := by
  have h := Real.one_sub_lt_exp_neg hv.ne'
  linarith

private theorem B_pos {v : ℝ} (hv : 0 < v) : 0 < B v := by
  rw [B_closed hv]
  exact div_pos
    (mul_pos (mul_pos (actualPhi_pos v) (Real.exp_pos (-v)))
      (exp_remainder_pos hv)) (pow_pos hv 2)

private def D (v : ℝ) : ℝ :=
  1 + v - v ^ 2 - 3 * v * Real.exp (-v) - Real.exp (-v) ^ 2

private def T0 (v : ℝ) : ℝ :=
  (v ^ 2 - v - 1) * Real.exp (2 * v) + 3 * v * Real.exp v + 1

private def T1 (v : ℝ) : ℝ :=
  (2 * v ^ 2 - 3) * Real.exp (2 * v) + 3 * (v + 1) * Real.exp v

private def T2 (v : ℝ) : ℝ :=
  (4 * v ^ 2 + 4 * v - 6) * Real.exp (2 * v) + 3 * (v + 2) * Real.exp v

private def T3 (v : ℝ) : ℝ :=
  (8 * v ^ 2 + 16 * v - 8) * Real.exp (2 * v) + 3 * (v + 3) * Real.exp v

private def T4 (v : ℝ) : ℝ :=
  (16 * v ^ 2 + 48 * v) * Real.exp (2 * v) + 3 * (v + 4) * Real.exp v

private theorem hasDerivAt_T0 (v : ℝ) : HasDerivAt T0 (T1 v) v := by
  have hp := (((hasDerivAt_id v).pow 2).sub (hasDerivAt_id v)).sub_const 1
  have he := ((hasDerivAt_id v).const_mul 2).exp
  have hl := ((hasDerivAt_id v).const_mul 3).mul (Real.hasDerivAt_exp v)
  have h := ((hp.mul he).add hl).add_const 1
  unfold T0
  apply h.congr_deriv
  unfold T1
  norm_num
  ring

private theorem hasDerivAt_T1 (v : ℝ) : HasDerivAt T1 (T2 v) v := by
  have hp := (((hasDerivAt_id v).pow 2).const_mul 2).sub_const 3
  have he := ((hasDerivAt_id v).const_mul 2).exp
  have hl := (((hasDerivAt_id v).add_const 1).const_mul 3).mul
    (Real.hasDerivAt_exp v)
  have h := (hp.mul he).add hl
  unfold T1
  apply h.congr_deriv
  unfold T2
  norm_num
  ring

private theorem hasDerivAt_T2 (v : ℝ) : HasDerivAt T2 (T3 v) v := by
  have hp := ((((hasDerivAt_id v).pow 2).const_mul 4).add
    ((hasDerivAt_id v).const_mul 4)).sub_const 6
  have he := ((hasDerivAt_id v).const_mul 2).exp
  have hl := (((hasDerivAt_id v).add_const 2).const_mul 3).mul
    (Real.hasDerivAt_exp v)
  have h := (hp.mul he).add hl
  unfold T2
  apply h.congr_deriv
  unfold T3
  norm_num
  ring

private theorem hasDerivAt_T3 (v : ℝ) : HasDerivAt T3 (T4 v) v := by
  have hp := ((((hasDerivAt_id v).pow 2).const_mul 8).add
    ((hasDerivAt_id v).const_mul 16)).sub_const 8
  have he := ((hasDerivAt_id v).const_mul 2).exp
  have hl := (((hasDerivAt_id v).add_const 3).const_mul 3).mul
    (Real.hasDerivAt_exp v)
  have h := (hp.mul he).add hl
  unfold T3
  apply h.congr_deriv
  unfold T4
  norm_num
  ring

private theorem T4_pos {v : ℝ} (hv : 0 ≤ v) : 0 < T4 v := by
  have hp : 0 ≤ 16 * v ^ 2 + 48 * v := by nlinarith [sq_nonneg v]
  have hfirst : 0 ≤ (16 * v ^ 2 + 48 * v) * Real.exp (2 * v) :=
    mul_nonneg hp (Real.exp_pos (2 * v)).le
  have hlast : 0 < 3 * (v + 4) * Real.exp v := by positivity
  unfold T4
  linarith

private theorem T3_strictMonoOn : StrictMonoOn T3 (Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
    (show ContinuousOn T3 (Ici (0 : ℝ)) from
      (show Continuous T3 by unfold T3; fun_prop).continuousOn)
  intro v hv
  have hv0 : 0 < v := by simpa only [interior_Ici, mem_Ioi] using hv
  rw [(hasDerivAt_T3 v).deriv]
  exact T4_pos hv0.le

private theorem T3_pos {v : ℝ} (hv : 0 < v) : 0 < T3 v := by
  have h := T3_strictMonoOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hv.le) hv
  have hz : T3 0 = 1 := by norm_num [T3]
  linarith

private theorem T2_strictMonoOn : StrictMonoOn T2 (Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
    (show ContinuousOn T2 (Ici (0 : ℝ)) from
      (show Continuous T2 by unfold T2; fun_prop).continuousOn)
  intro v hv
  have hv0 : 0 < v := by simpa only [interior_Ici, mem_Ioi] using hv
  rw [(hasDerivAt_T2 v).deriv]
  exact T3_pos hv0

private theorem T2_pos {v : ℝ} (hv : 0 < v) : 0 < T2 v := by
  have h := T2_strictMonoOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hv.le) hv
  have hz : T2 0 = 0 := by norm_num [T2]
  linarith

private theorem T1_strictMonoOn : StrictMonoOn T1 (Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
    (show ContinuousOn T1 (Ici (0 : ℝ)) from
      (show Continuous T1 by unfold T1; fun_prop).continuousOn)
  intro v hv
  have hv0 : 0 < v := by simpa only [interior_Ici, mem_Ioi] using hv
  rw [(hasDerivAt_T1 v).deriv]
  exact T2_pos hv0

private theorem T1_pos {v : ℝ} (hv : 0 < v) : 0 < T1 v := by
  have h := T1_strictMonoOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hv.le) hv
  have hz : T1 0 = 0 := by norm_num [T1]
  linarith

private theorem T0_strictMonoOn : StrictMonoOn T0 (Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
    (show ContinuousOn T0 (Ici (0 : ℝ)) from
      (show Continuous T0 by unfold T0; fun_prop).continuousOn)
  intro v hv
  have hv0 : 0 < v := by simpa only [interior_Ici, mem_Ioi] using hv
  rw [(hasDerivAt_T0 v).deriv]
  exact T1_pos hv0

private theorem T0_pos {v : ℝ} (hv : 0 < v) : 0 < T0 v := by
  have h := T0_strictMonoOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hv.le) hv
  have hz : T0 0 = 0 := by norm_num [T0]
  linarith

private theorem T0_eq_neg_exp_mul_D (v : ℝ) :
    T0 v = -Real.exp (2 * v) * D v := by
  have he : Real.exp (2 * v) = Real.exp v * Real.exp v := by
    rw [show (2 : ℝ) * v = v + v by ring, Real.exp_add]
  unfold T0 D
  simp only [he, Real.exp_neg]
  field_simp [Real.exp_ne_zero v]
  <;> ring

private theorem D_neg {v : ℝ} (hv : 0 < v) : D v < 0 := by
  have h := T0_pos hv
  rw [T0_eq_neg_exp_mul_D] at h
  by_contra hn
  have hn0 : 0 ≤ D v := le_of_not_gt hn
  have hm : 0 ≤ Real.exp (2 * v) * D v :=
    mul_nonneg (Real.exp_pos (2 * v)).le hn0
  nlinarith

private theorem hasDerivAt_B {v : ℝ} (hv : 0 < v) :
    HasDerivAt B
      (B v * D v / (v * (v - 1 + Real.exp (-v)))) v := by
  let a : ℝ → ℝ := fun w => w - 1 + Real.exp (-w)
  have ha : HasDerivAt a (1 - Real.exp (-v)) v := by
    have h := ((hasDerivAt_id v).sub_const 1).add ((hasDerivAt_id v).neg.exp)
    apply h.congr_deriv
    dsimp
    ring
  have h := (((hasDerivAt_actualPhi v).mul
    ((hasDerivAt_id v).neg.exp)).mul ha).div
      ((hasDerivAt_id v).pow 2) (pow_ne_zero 2 hv.ne')
  have hclosed : HasDerivAt
      (fun w : ℝ => actualPhi w * Real.exp (-w) *
        (w - 1 + Real.exp (-w)) / w ^ 2)
      (B v * D v / (v * (v - 1 + Real.exp (-v)))) v := by
    apply h.congr_deriv
    dsimp [a]
    rw [rate_eq hv.ne', B_closed hv]
    unfold D
    field_simp [hv.ne', (exp_remainder_pos hv).ne']
    <;> ring
  apply hclosed.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hv] with w hw
  exact B_closed (show 0 < w from hw)

private theorem B_strictAntiOn : StrictAntiOn B (Ici (0 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ)) continuous_B.continuousOn
  intro v hv
  have hv0 : 0 < v := by simpa only [interior_Ici, mem_Ioi] using hv
  rw [(hasDerivAt_B hv0).deriv]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (B_pos hv0) (D_neg hv0))
    (mul_pos hv0 (exp_remainder_pos hv0))

private theorem B_lt_half {v : ℝ} (hv : 0 < v) : B v < 1 / 2 := by
  have h := B_strictAntiOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hv.le) hv
  simpa only [B_zero] using h

/-- The literal prime-prefix Phi has positive, strictly decreasing curvature on Ici 0. -/
theorem result :
    deriv (deriv actualPhi) 0 = (1 / 2 : ℝ) ∧
      StrictAntiOn (deriv (deriv actualPhi)) (Ici (0 : ℝ)) ∧
      (∀ v : ℝ, 0 < v →
        0 < deriv (deriv actualPhi) v ∧ deriv (deriv actualPhi) v < 1 / 2) := by
  have hfun : deriv (deriv actualPhi) = B := by
    funext v
    exact actualPhi_second_derivative v
  rw [hfun]
  exact ⟨B_zero, B_strictAntiOn, fun v hv => ⟨B_pos hv, B_lt_half hv⟩⟩


end D5.S3.Arith.Robin.PrimePrefixPhiCurvature

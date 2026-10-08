/- GID: D5/S3/Arith/Robin/PrimePrefixCurvatureVolterraRecursion
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PrimePrefixCurvatureVolterraRecursion
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The literal curvature satisfies an exact positive Volterra equation and has strictly increasing recursive floors with exact iterated residuals. -/

import D5.S3.Arith.Robin.PrimePrefixPhiCurvature
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-!
The literal Phi and first derivative retain PrimorialGlobalLaplaceEnvelope
provenance. The complete all-real rate derivative, curvature binding and
positive-axis closed curvature chain below are consumed copies from
PrimePrefixCurvatureExponentialFloor, originally PrimePrefixPhiCurvature
and PrimorialFirstOrderConcentrationCounterexample. Private helpers are
copied because the public results do not expose their needed exact bodies.

The new continuous coefficient is defined by its actual finite integral.
A weighted-exponential primitive proves its positive-axis closed formula,
so zero continuity is proved rather than assumed. The coefficient and two
finite FTC identities yield B=b+TB for the same literal second derivative.
The equation is consumed by recursive floors, exact iterated residuals,
and strict finite-layer improvement. No signed Robin transport is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter MeasureTheory
open scoped Topology Interval
open D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope

namespace D5.S3.Arith.Robin.PrimePrefixCurvatureVolterraRecursion

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


private def tiltedB (v : ℝ) : ℝ := Real.exp v * B v

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

/-- The actual continuous coefficient of the literal curvature recursion. -/
def coefficient (v : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1, (1-t)^2 *
    (Real.exp (-v*(1-t)) + Real.exp (-v*(1+t)))) / 2

/-- Finite second integration, retaining the original input function. -/
def lift (f : ℝ → ℝ) (v : ℝ) : ℝ := ∫ t in (0 : ℝ)..v, (v-t)*f t

/-- The explicit positive source in the literal Volterra equation. -/
def floor (v : ℝ) : ℝ :=
  Real.exp (-v) * (1/2 + ∫ s in (0 : ℝ)..v, coefficient s*(1+s))

/-- The exact finite Volterra operator, with no unbounded input integral. -/
def volterra (f : ℝ → ℝ) (v : ℝ) : ℝ :=
  Real.exp (-v) * ∫ s in (0 : ℝ)..v, coefficient s * lift f s

/-- Actual finite recursive floors: the source and operator are fixed above. -/
def approximation : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n+1 => fun v => floor v + volterra (approximation n) v

/-- The same literal second derivative supplied by the original Phi. -/
def curvature (v : ℝ) : ℝ := deriv (deriv actualPhi) v

/-- Exact remainder in the actual curvature, rather than an abstract solution. -/
def residual (n : ℕ) (v : ℝ) : ℝ := curvature v - approximation n v

private theorem continuous_coefficient : Continuous coefficient := by
  unfold coefficient
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (show Continuous (fun p : ℝ × ℝ => (1-p.2)^2 *
      (Real.exp (-p.1*(1-p.2)) + Real.exp (-p.1*(1+p.2)))) by fun_prop)
    0 1).div_const 2

private theorem weight_integral :
    (∫ t in (0 : ℝ)..1, (1-t)^2) = (1/3 : ℝ) := by
  have hd (t : ℝ) :
      HasDerivAt (fun x : ℝ => -(1-x)^3/3) ((1-t)^2) t := by
    have h := ((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).pow 3).neg).div_const 3
    apply h.congr_deriv
    norm_num
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t)
    ((show Continuous (fun t : ℝ => (1-t)^2) by fun_prop).intervalIntegrable 0 1)
      (a := (0 : ℝ)) (b := 1)
  norm_num at h
  exact h

private theorem coefficient_zero : coefficient 0 = (1/3 : ℝ) := by
  unfold coefficient
  have hfun : (fun t : ℝ => (1-t)^2 *
      (Real.exp (-(0 : ℝ)*(1-t)) + Real.exp (-(0 : ℝ)*(1+t)))) =
      fun t : ℝ => 2*((1-t)^2) := by
    funext t
    simp
    ring
  rw [hfun, intervalIntegral.integral_const_mul, weight_integral]
  norm_num

private theorem coefficient_pos (v : ℝ) : 0 < coefficient v := by
  unfold coefficient
  apply div_pos _ (by norm_num)
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((show Continuous (fun t : ℝ => (1-t)^2 *
      (Real.exp (-v*(1-t)) + Real.exp (-v*(1+t)))) by fun_prop).intervalIntegrable 0 1)
  · intro t ht
    exact mul_pos (pow_pos (sub_pos.mpr ht.2) 2)
      (add_pos (Real.exp_pos _) (Real.exp_pos _))
  · norm_num

private theorem coefficient_le_third {v : ℝ} (hv : 0 ≤ v) :
    coefficient v ≤ (1/3 : ℝ) := by
  have hint := intervalIntegral.integral_mono_on (μ := volume) (zero_le_one' ℝ)
    ((show Continuous (fun t : ℝ => (1-t)^2 *
      (Real.exp (-v*(1-t)) + Real.exp (-v*(1+t)))) by fun_prop).intervalIntegrable 0 1)
    ((show Continuous (fun t : ℝ => 2*(1-t)^2) by fun_prop).intervalIntegrable 0 1)
    (fun t ht => by
      have he1 : Real.exp (-v*(1-t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [ht.1, ht.2])
      have he2 : Real.exp (-v*(1+t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
      have hm := mul_le_mul_of_nonneg_left (add_le_add he1 he2) (sq_nonneg (1-t))
      nlinarith)
  rw [intervalIntegral.integral_const_mul, weight_integral] at hint
  unfold coefficient
  linarith

/-- A direct finite primitive pays the coefficient's closed formula. -/
private theorem weighted_exponential_integral {z : ℝ} (hz : z ≠ 0) :
    (∫ t in (0 : ℝ)..1, (1-t)^2 * Real.exp (z*t)) =
      (2*Real.exp z-z^2-2*z-2)/z^3 := by
  let P : ℝ → ℝ := fun t => Real.exp (z*t) *
    ((1-t)^2/z + 2*(1-t)/z^2 + 2/z^3)
  have hd (t : ℝ) : HasDerivAt P ((1-t)^2 * Real.exp (z*t)) t := by
    have ha := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).pow 2
    have hb := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).const_mul 2)
    have hp := ((ha.div_const z).add (hb.div_const (z^2))).add_const (2/z^3)
    have he := ((hasDerivAt_id t).const_mul z).exp
    have h := he.mul hp
    apply h.congr_deriv
    dsimp [P]
    field_simp [hz]
    <;> ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t)
    ((show Continuous (fun t : ℝ => (1-t)^2 * Real.exp (z*t)) by fun_prop).intervalIntegrable 0 1)
    (a := (0 : ℝ)) (b := 1)
  rw [h]
  dsimp [P]
  simp only [mul_one, mul_zero, Real.exp_zero, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_div, mul_zero, zero_add, sub_zero, one_pow, one_mul]
  field_simp [hz]
  <;> ring

private theorem coefficient_closed {v : ℝ} (hv : 0 < v) :
    coefficient v = Real.exp (-v)*(Real.exp v-Real.exp (-v)-2*v)/v^3 := by
  have hfun : (fun t : ℝ => (1-t)^2 *
      (Real.exp (-v*(1-t)) + Real.exp (-v*(1+t)))) =
      fun t : ℝ => Real.exp (-v)*
        ((1-t)^2*Real.exp (v*t) + (1-t)^2*Real.exp ((-v)*t)) := by
    funext t
    rw [show -v*(1-t) = -v+v*t by ring,
      show -v*(1+t) = -v+(-v)*t by ring, Real.exp_add, Real.exp_add]
    ring
  unfold coefficient
  rw [hfun, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add
      ((show Continuous (fun t : ℝ => (1-t)^2*Real.exp (v*t)) by fun_prop).intervalIntegrable 0 1)
      ((show Continuous (fun t : ℝ => (1-t)^2*Real.exp ((-v)*t)) by fun_prop).intervalIntegrable 0 1),
    weighted_exponential_integral hv.ne',
    weighted_exponential_integral (neg_ne_zero.mpr hv.ne')]
  field_simp [hv.ne']
  <;> ring

private theorem curvature_eq_B (v : ℝ) : curvature v = B v :=
  actualPhi_second_derivative v

private theorem continuous_curvature : Continuous curvature := by
  have hf : curvature = B := funext curvature_eq_B
  rw [hf]
  exact continuous_B

private theorem curvature_zero : curvature 0 = (1/2 : ℝ) := by
  rw [curvature_eq_B, B_zero]

private theorem curvature_pos {v : ℝ} (hv : 0 < v) : 0 < curvature v :=
  (PrimePrefixPhiCurvature.result.2.2 v hv).1

private theorem continuous_lift {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (lift f) := by
  unfold lift
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (show Continuous (fun p : ℝ × ℝ => (p.1-p.2)*f p.2) by fun_prop)
    continuous_id

private theorem continuous_floor : Continuous floor := by
  unfold floor
  apply (Real.continuous_exp.comp continuous_neg).mul
  apply continuous_const.add
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (show Continuous (fun p : ℝ × ℝ => coefficient p.2*(1+p.2)) by
      exact (continuous_coefficient.comp continuous_snd).mul (continuous_const.add continuous_snd))
    continuous_id

private theorem continuous_volterra {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (volterra f) := by
  unfold volterra
  apply (Real.continuous_exp.comp continuous_neg).mul
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (show Continuous (fun p : ℝ × ℝ => coefficient p.2*lift f p.2) from
      (continuous_coefficient.comp continuous_snd).mul ((continuous_lift hf).comp continuous_snd))
    continuous_id

private theorem phi_lift (v : ℝ) : actualPhi v = 1+v+lift curvature v := by
  let P : ℝ → ℝ := fun t =>
    (v-t)*(actualPhi t*rate t)+actualPhi t
  have hd (t : ℝ) : HasDerivAt P ((v-t)*B t) t := by
    have h := (((hasDerivAt_const t v).sub (hasDerivAt_id t)).mul
      (hasDerivAt_phi_slope t)).add (hasDerivAt_actualPhi t)
    apply h.congr_deriv
    dsimp [P]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t)
    ((show Continuous (fun t : ℝ => (v-t)*B t) from
      (continuous_const.sub continuous_id).mul continuous_B).intervalIntegrable 0 v)
    (a := (0 : ℝ)) (b := v)
  dsimp [P] at h
  simp only [sub_self, zero_mul, zero_add, sub_zero, actualPhi_zero, rate_zero,
    one_mul, mul_one] at h
  have hfun : curvature = B := funext curvature_eq_B
  rw [lift, hfun]
  linarith

private theorem hasDerivAt_tiltedB_coefficient {v : ℝ} (hv : 0 < v) :
    HasDerivAt tiltedB (coefficient v*actualPhi v) v := by
  apply (hasDerivAt_tiltedB hv).congr_deriv
  rw [coefficient_closed hv]
  have he : Real.exp (-v)*Real.exp v = 1 := by
    rw [← Real.exp_add]
    simp
  have hid : 1-2*v*Real.exp (-v)-Real.exp (-v)^2 =
      Real.exp (-v)*(Real.exp v-Real.exp (-v)-2*v) := by
    nlinarith [he]
  rw [hid]
  ring

private theorem curvature_integral {v : ℝ} (hv : 0 ≤ v) :
    curvature v = Real.exp (-v)*
      (1/2 + ∫ s in (0 : ℝ)..v, coefficient s*actualPhi s) := by
  have hc : Continuous tiltedB := Real.continuous_exp.mul continuous_B
  have hi : Continuous (fun s : ℝ => coefficient s*actualPhi s) :=
    continuous_coefficient.mul continuous_actualPhi
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hv hc.continuousOn
    (fun s hs => hasDerivAt_tiltedB_coefficient hs.1) (hi.intervalIntegrable 0 v)
  have hz : tiltedB 0 = (1/2 : ℝ) := by simp [tiltedB, B_zero]
  rw [hz] at h
  have he : Real.exp (-v)*Real.exp v = 1 := by
    rw [← Real.exp_add]
    simp
  have hsum : 1/2 + (∫ s in (0 : ℝ)..v, coefficient s*actualPhi s) = tiltedB v := by
    linarith
  rw [hsum]
  rw [curvature_eq_B]
  unfold tiltedB
  rw [← mul_assoc, he, one_mul]

private theorem actual_equation {v : ℝ} (hv : 0 ≤ v) :
    curvature v = floor v+volterra curvature v := by
  rw [curvature_integral hv]
  have heq : (fun s : ℝ => coefficient s*actualPhi s) =
      fun s => coefficient s*(1+s)+coefficient s*lift curvature s := by
    funext s
    rw [phi_lift s]
    ring
  have h1 : IntervalIntegrable (fun s : ℝ => coefficient s*(1+s)) volume 0 v :=
    (show Continuous (fun s : ℝ => coefficient s*(1+s)) from
      continuous_coefficient.mul (continuous_const.add continuous_id)).intervalIntegrable 0 v
  have h2 : IntervalIntegrable (fun s : ℝ => coefficient s*lift curvature s) volume 0 v :=
    (show Continuous (fun s : ℝ => coefficient s*lift curvature s) from
      continuous_coefficient.mul (continuous_lift continuous_curvature)).intervalIntegrable 0 v
  rw [heq, intervalIntegral.integral_add h1 h2]
  unfold floor volterra
  ring

private theorem lift_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (v : ℝ) :
    lift (fun t => f t-g t) v = lift f v-lift g v := by
  unfold lift
  have heq : (fun t : ℝ => (v-t)*(f t-g t)) =
      fun t => (v-t)*f t-(v-t)*g t := by funext t; ring
  have h1 : IntervalIntegrable (fun t : ℝ => (v-t)*f t) volume 0 v :=
    (show Continuous (fun t : ℝ => (v-t)*f t) from
      (continuous_const.sub continuous_id).mul hf).intervalIntegrable 0 v
  have h2 : IntervalIntegrable (fun t : ℝ => (v-t)*g t) volume 0 v :=
    (show Continuous (fun t : ℝ => (v-t)*g t) from
      (continuous_const.sub continuous_id).mul hg).intervalIntegrable 0 v
  rw [heq, intervalIntegral.integral_sub h1 h2]

private theorem volterra_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (v : ℝ) :
    volterra (fun t => f t-g t) v = volterra f v-volterra g v := by
  unfold volterra
  have heq : (fun s : ℝ => coefficient s*lift (fun t => f t-g t) s) =
      fun s => coefficient s*lift f s-coefficient s*lift g s := by
    funext s
    rw [lift_sub hf hg]
    ring
  have h1 : IntervalIntegrable (fun s : ℝ => coefficient s*lift f s) volume 0 v :=
    (show Continuous (fun s : ℝ => coefficient s*lift f s) from
      continuous_coefficient.mul (continuous_lift hf)).intervalIntegrable 0 v
  have h2 : IntervalIntegrable (fun s : ℝ => coefficient s*lift g s) volume 0 v :=
    (show Continuous (fun s : ℝ => coefficient s*lift g s) from
      continuous_coefficient.mul (continuous_lift hg)).intervalIntegrable 0 v
  rw [heq, intervalIntegral.integral_sub h1 h2]
  ring

private theorem volterra_congr_nonnegative {f g : ℝ → ℝ}
    (hfg : ∀ v : ℝ, 0 ≤ v → f v = g v) {v : ℝ} (hv : 0 ≤ v) :
    volterra f v = volterra g v := by
  unfold volterra lift
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le hv
  intro s hs
  change coefficient s*(∫ t in (0 : ℝ)..s, (s-t)*f t) =
    coefficient s*(∫ t in (0 : ℝ)..s, (s-t)*g t)
  apply congrArg (fun x : ℝ => coefficient s*x)
  apply intervalIntegral.integral_congr_Ioo_of_le hs.1.le
  intro t ht
  change (s-t)*f t = (s-t)*g t
  rw [hfg t ht.1.le]

private theorem lift_nonnegative {f : ℝ → ℝ}
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ lift f v := by
  unfold lift
  exact intervalIntegral.integral_nonneg hv
    (fun t ht => mul_nonneg (sub_nonneg.mpr ht.2) (hpos t ht.1))

private theorem volterra_nonnegative {f : ℝ → ℝ}
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ volterra f v := by
  unfold volterra
  apply mul_nonneg (Real.exp_pos _).le
  exact intervalIntegral.integral_nonneg hv (fun s hs =>
    mul_nonneg (coefficient_pos s).le (lift_nonnegative hpos hs.1))

private theorem lift_positive {f : ℝ → ℝ} (hf : Continuous f)
    (hpos : ∀ t : ℝ, 0 < t → 0 < f t) {v : ℝ} (hv : 0 < v) :
    0 < lift f v := by
  unfold lift
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    (((continuous_const.sub continuous_id).mul hf).intervalIntegrable 0 v)
    (fun t ht => mul_pos (sub_pos.mpr ht.2) (hpos t ht.1)) hv

private theorem volterra_positive {f : ℝ → ℝ} (hf : Continuous f)
    (hpos : ∀ t : ℝ, 0 < t → 0 < f t) {v : ℝ} (hv : 0 < v) :
    0 < volterra f v := by
  unfold volterra
  apply mul_pos (Real.exp_pos _)
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_coefficient.mul (continuous_lift hf)).intervalIntegrable 0 v)
    (fun s hs => mul_pos (coefficient_pos s) (lift_positive hf hpos hs.1)) hv

private theorem floor_positive {v : ℝ} (hv : 0 ≤ v) : 0 < floor v := by
  have hi : 0 ≤ ∫ s in (0 : ℝ)..v, coefficient s*(1+s) :=
    intervalIntegral.integral_nonneg hv (fun s hs =>
      mul_nonneg (coefficient_pos s).le (by linarith [hs.1]))
  unfold floor
  exact mul_pos (Real.exp_pos _) (by linarith)

private theorem continuous_approximation (n : ℕ) : Continuous (approximation n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact continuous_floor.add (continuous_volterra ih)

private theorem continuous_residual (n : ℕ) : Continuous (residual n) :=
  continuous_curvature.sub (continuous_approximation n)

private theorem residual_step (n : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    residual (n+1) v = volterra (residual n) v := by
  unfold residual
  rw [actual_equation hv]
  change floor v+volterra curvature v-
    (floor v+volterra (approximation n) v) =
      volterra (fun t => curvature t-approximation n t) v
  rw [volterra_sub continuous_curvature (continuous_approximation n)]
  ring

private theorem residual_iterate (n : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    residual n v = (volterra^[n] curvature) v := by
  induction n generalizing v with
  | zero => simp [residual, approximation]
  | succ n ih =>
    rw [residual_step n hv, Function.iterate_succ_apply']
    exact volterra_congr_nonnegative (fun t ht => ih ht) hv

private theorem residual_positive (n : ℕ) {v : ℝ} (hv : 0 < v) :
    0 < residual n v := by
  induction n generalizing v with
  | zero => simpa [residual, approximation] using curvature_pos hv
  | succ n ih =>
    rw [residual_step n hv.le]
    exact volterra_positive (continuous_residual n) (fun t ht => ih ht) hv

private def increment (n : ℕ) (v : ℝ) : ℝ :=
  approximation (n+1) v-approximation n v

private theorem continuous_increment (n : ℕ) : Continuous (increment n) :=
  (continuous_approximation (n+1)).sub (continuous_approximation n)

private theorem increment_step (n : ℕ) (v : ℝ) :
    increment (n+1) v = volterra (increment n) v := by
  change floor v+volterra (approximation (n+1)) v-
    (floor v+volterra (approximation n) v) =
      volterra (fun t => approximation (n+1) t-approximation n t) v
  rw [volterra_sub (continuous_approximation (n+1)) (continuous_approximation n)]
  ring

private theorem increment_positive (n : ℕ) {v : ℝ} (hv : 0 < v) :
    0 < increment n v := by
  induction n generalizing v with
  | zero => simpa [increment, approximation, volterra, lift] using floor_positive hv.le
  | succ n ih =>
    rw [increment_step]
    exact volterra_positive (continuous_increment n) (fun t ht => ih ht) hv

private theorem approximation_nonnegative (n : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ approximation n v := by
  induction n generalizing v with
  | zero => simp [approximation]
  | succ n ih =>
    exact add_nonneg (floor_positive hv).le (volterra_nonnegative (fun t ht => ih ht) hv)

private theorem approximation_strict_chain (n : ℕ) {v : ℝ} (hv : 0 < v) :
    0 ≤ approximation n v ∧ approximation n v < approximation (n+1) v ∧
      approximation (n+1) v < curvature v := by
  refine ⟨approximation_nonnegative n hv.le, ?_, ?_⟩
  · exact sub_pos.mp (increment_positive n hv)
  · exact sub_pos.mp (residual_positive (n+1) hv)

private theorem approximation_succ_zero (n : ℕ) : approximation (n+1) 0 = (1/2 : ℝ) := by
  simp [approximation, floor, volterra]

private theorem residual_succ_zero (n : ℕ) : residual (n+1) 0 = 0 := by
  rw [residual, curvature_zero, approximation_succ_zero]
  ring

/-- The exact literal Volterra equation is consumed by strict recursive actual floors. -/
theorem result :
    Continuous coefficient ∧ coefficient 0 = (1/3 : ℝ) ∧
    (∀ v : ℝ, 0 ≤ v → 0 < coefficient v ∧ coefficient v ≤ 1/3) ∧
    (∀ v : ℝ, 0 ≤ v →
      actualPhi v = 1+v+lift curvature v ∧
      curvature v = Real.exp (-v)*
        (1/2 + ∫ s in (0 : ℝ)..v, coefficient s*actualPhi s) ∧
      curvature v = floor v+volterra curvature v) ∧
    (∀ (n : ℕ) (v : ℝ), 0 ≤ v → residual n v = (volterra^[n] curvature) v) ∧
    (∀ (n : ℕ) (v : ℝ), 0 < v →
      0 ≤ approximation n v ∧ approximation n v < approximation (n+1) v ∧
      approximation (n+1) v < curvature v) ∧
    (∀ n : ℕ, approximation (n+1) 0 = (1/2 : ℝ) ∧ residual (n+1) 0 = 0) := by
  refine ⟨continuous_coefficient, coefficient_zero, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact ⟨coefficient_pos v, coefficient_le_third hv⟩
  · intro v hv
    exact ⟨phi_lift v, curvature_integral hv, actual_equation hv⟩
  · intro n v hv
    exact residual_iterate n hv
  · intro n v hv
    exact approximation_strict_chain n hv
  · intro n
    exact ⟨approximation_succ_zero n, residual_succ_zero n⟩

end D5.S3.Arith.Robin.PrimePrefixCurvatureVolterraRecursion

#print axioms D5.S3.Arith.Robin.PrimePrefixCurvatureVolterraRecursion.result

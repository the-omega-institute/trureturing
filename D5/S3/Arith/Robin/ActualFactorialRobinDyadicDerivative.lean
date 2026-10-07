/- GID: D5/S3/Arith/Robin/ActualFactorialRobinDyadicDerivative
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualFactorialRobinDyadicDerivative
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The original factorial Robin integral has an exact complete low and high decomposition and a genuine dyadic derivative with a signed error and a uniform logarithmic-ratio bound. -/

import D5.S3.Arith.Robin.ActualFactorialRobinHighDerivative
import D5.S3.Arith.Robin.QuotientIntegralBudget
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
N-only source candidate. The physical Robin integral below uses the actual eta
and weight at their unique existing owners. The entire high-domain derivative
is the preceding actual high-integral theorem. The low-domain formula directly
consumes QuotientIntegralBudget.residual_at_most_one at its original owner;
its additional original-owner visibility candidate must be installed in place.

The proof pays the actual physical change of variables, both integrabilities,
the exact complete low/high decomposition, and the derivative of the same
dyadic weight s*(P_x(s)-P_x(2s)). No arithmetic cancellation, harmonic decay,
infinite Mobius-tail sign or RH conclusion is assumed or proved here.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval

namespace D5.S3.Arith.Robin.ActualFactorialRobinDyadicDerivative

open D5.S3.Arith.Robin.ActualFactorialRobinHighDerivative
  (eta kernelData highKernel highIntegrand highRemainder highRemainderDerivative)
open D5.S3.Arith.Robin.MellinWeightedVariation (weight scaleWeight_eq)
open D5.S3.Arith.Robin.QuotientIntegralBudget (residual_at_most_one)

def physicalIntegrand (s t : ℝ) : ℝ := eta (t / s) * weight t

/-- The original physical Robin integral, with its complete factorial remainder. -/
def P (x s : ℝ) : ℝ := ∫ t in Ioi x, physicalIntegrand s t

/-- The original complete dyadic growth weight. -/
def b (x s : ℝ) : ℝ := s * (P x s - P x (2 * s))

def lowPrimitive (ell r : ℝ) : ℝ :=
  r * Real.log r + (ell⁻¹ - Real.log ell - 1) * r +
    (ell⁻¹ + ell - 1) - r⁻¹

private def lowDensity (r t : ℝ) : ℝ :=
  (1 + r) * (t⁻¹ / (Real.log t) ^ 2) + r * (t⁻¹ / Real.log t) - t⁻¹

private def lowPrimitiveDerivative (ell r : ℝ) : ℝ :=
  Real.log r + 1 + (ell⁻¹ - Real.log ell - 1) + r⁻¹ ^ 2

def mainDerivative (ell r : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (r / ell) + 1 / (2 * ell) -
    (1 / 2 : ℝ) * Real.log (1 + Real.log 2 / r) +
    r⁻¹ ^ 2 - (1 / 2 : ℝ) * (r + Real.log 2)⁻¹ ^ 2

def bDerivative (x s : ℝ) : ℝ :=
  (mainDerivative (Real.log x) (Real.log s) + highRemainderDerivative (Real.log s) -
    (1 / 2 : ℝ) * highRemainderDerivative (Real.log s + Real.log 2)) / s

private lemma eta_low {y : ℝ} (hy : y ≤ 1) : eta y = y * (1 - Real.log y) := by
  have h := residual_at_most_one kernelData hy
  change eta y = 1 * y - 1 * (y * Real.log y) at h
  rw [h]
  ring

private lemma low_pointwise {x s t : ℝ} (hx : 1 < x) (hxs : x ≤ s)
    (ht : t ∈ Icc x s) : s * physicalIntegrand s t = lowDensity (Real.log s) t := by
  have ht1 : 1 < t := hx.trans_le ht.1
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < s := by linarith
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have hquot : t / s ≤ 1 := (div_le_one hs0).mpr ht.2
  unfold physicalIntegrand
  rw [eta_low hquot, Real.log_div ht0.ne' hs0.ne']
  unfold weight lowDensity
  field_simp [hs0.ne', ht0.ne', hlog.ne']
  <;> ring

private lemma low_integrable {x s r : ℝ} (hx : 1 < x) (hxs : x ≤ s) :
    IntervalIntegrable (lowDensity r) volume x s := by
  apply ContinuousOn.intervalIntegrable_of_Icc hxs
  intro t ht
  have ht1 : 1 < t := hx.trans_le ht.1
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht1
  have hi : ContinuousAt (fun u : ℝ => u⁻¹) t := continuousAt_id.inv₀ ht0.ne'
  have hg : ContinuousAt Real.log t := Real.continuousAt_log ht0.ne'
  exact (((hi.div (hg.pow 2) (pow_ne_zero 2 hl.ne')).const_mul (1 + r)).add
    ((hi.div hg hl.ne').const_mul r)).sub hi |>.continuousWithinAt

private lemma low_physical_integrable {x s : ℝ} (hx : 1 < x) (hxs : x ≤ s) :
    IntervalIntegrable (physicalIntegrand s) volume x s := by
  have hs0 : 0 < s := by linarith
  have hg := (intervalIntegrable_iff_integrableOn_Ioc_of_le hxs).mp
    (low_integrable (r := Real.log s) hx hxs)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hxs).mpr
  apply IntegrableOn.congr_fun (hg.const_mul s⁻¹) _ measurableSet_Ioc
  intro t ht
  have hp := low_pointwise hx hxs (show t ∈ Icc x s from ⟨ht.1.le, ht.2⟩)
  dsimp
  rw [← hp]
  field_simp [hs0.ne']

private lemma low_integral {x s : ℝ} (hx : 1 < x) (hxs : x ≤ s) :
    s * (∫ t in x..s, physicalIntegrand s t) = lowPrimitive (Real.log x) (Real.log s) := by
  have hs1 : 1 < s := hx.trans_le hxs
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < s := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hls : 0 < Real.log s := Real.log_pos hs1
  have hi : IntervalIntegrable (fun t : ℝ => t⁻¹) volume x s := by
    apply ContinuousOn.intervalIntegrable_of_Icc hxs
    intro t ht
    exact (continuousAt_id.inv₀ (show t ≠ 0 by linarith [ht.1])).continuousWithinAt
  have hg1 : IntervalIntegrable (fun t : ℝ => t⁻¹ / (Real.log t) ^ 2) volume x s := by
    apply ContinuousOn.intervalIntegrable_of_Icc hxs
    intro t ht
    have ht0 : 0 < t := hx0.trans_le ht.1
    have hl : 0 < Real.log t := Real.log_pos (hx.trans_le ht.1)
    exact ((continuousAt_id.inv₀ ht0.ne').div
      ((Real.continuousAt_log ht0.ne').pow 2) (pow_ne_zero 2 hl.ne')).continuousWithinAt
  have hg2 : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t) volume x s := by
    apply ContinuousOn.intervalIntegrable_of_Icc hxs
    intro t ht
    have ht0 : 0 < t := hx0.trans_le ht.1
    have hl : 0 < Real.log t := Real.log_pos (hx.trans_le ht.1)
    exact ((continuousAt_id.inv₀ ht0.ne').div
      (Real.continuousAt_log ht0.ne') hl.ne').continuousWithinAt
  calc
    _ = ∫ t in x..s, lowDensity (Real.log s) t := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hxs] at ht
      exact low_pointwise hx hxs ht
    _ = _ := by
      unfold lowDensity
      rw [intervalIntegral.integral_sub
        ((hg1.const_mul (1 + Real.log s)).add (hg2.const_mul (Real.log s))) hi,
        intervalIntegral.integral_add (hg1.const_mul (1 + Real.log s))
          (hg2.const_mul (Real.log s)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_inv_div_log_sq hx hs1, integral_inv_div_log hx hs1,
        integral_inv_of_pos hx0 hs0, Real.log_div hs0.ne' hx0.ne']
      unfold lowPrimitive
      field_simp [hlx.ne', hls.ne']
      <;> ring

private lemma high_scaled {s : ℝ} (hs : 1 < s) (y : ℝ) :
    highIntegrand (Real.log s) y = s ^ 2 * physicalIntegrand s (s * y) := by
  have hs0 : 0 < s := by linarith
  unfold highIntegrand highKernel physicalIntegrand
  rw [Real.exp_log hs0, scaleWeight_eq, mul_div_cancel_left₀ y hs0.ne']
  ring

private lemma high_physical_integrable {s : ℝ} (hs : 1 < s) :
    IntegrableOn (physicalIntegrand s) (Ioi s) := by
  have hs0 : 0 < s := by linarith
  have hr : 0 < Real.log s := Real.log_pos hs
  have hg :=
    (ActualFactorialRobinHighDerivative.result.2.2 (Real.log s) hr).1
  have hc : IntegrableOn (fun y : ℝ => physicalIntegrand s (s * y)) (Ioi (1 : ℝ)) := by
    apply IntegrableOn.congr_fun (hg.const_mul (s ^ 2)⁻¹) _ measurableSet_Ioi
    intro y _
    change (s ^ 2)⁻¹ * highIntegrand (Real.log s) y = physicalIntegrand s (s * y)
    rw [high_scaled hs]
    field_simp [hs0.ne']
  simpa only [mul_one] using
    (integrableOn_Ioi_comp_mul_left_iff (physicalIntegrand s) 1 hs0).mp hc

private lemma high_integral {s : ℝ} (hs : 1 < s) :
    s * (∫ t in Ioi s, physicalIntegrand s t) = highRemainder (Real.log s) := by
  have hs0 : 0 < s := by linarith
  have hscale := integral_comp_mul_left_Ioi' (physicalIntegrand s) 1 hs0
  simp only [smul_eq_mul, mul_one] at hscale
  calc
    _ = s ^ 2 * (∫ y in Ioi (1 : ℝ), physicalIntegrand s (s * y)) := by
      rw [← hscale]
      ring
    _ = highRemainder (Real.log s) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _
      exact (high_scaled hs y).symm

private lemma physical_integrable {x s : ℝ} (hx : 1 < x) (hxs : x ≤ s) :
    IntegrableOn (physicalIntegrand s) (Ioi x) := by
  have hl := (intervalIntegrable_iff_integrableOn_Ioc_of_le hxs).mp
    (low_physical_integrable hx hxs)
  have hh := high_physical_integrable (hx.trans_le hxs)
  simpa only [Ioc_union_Ioi_eq_Ioi hxs] using hl.union hh

private lemma normalized_identity {x s : ℝ} (hx : 1 < x) (hxs : x ≤ s) :
    s * P x s = lowPrimitive (Real.log x) (Real.log s) + highRemainder (Real.log s) := by
  have hsplit := intervalIntegral.integral_interval_add_Ioi'
    (low_physical_integrable hx hxs) (high_physical_integrable (hx.trans_le hxs))
  unfold P
  rw [← hsplit, mul_add, low_integral hx hxs, high_integral (hx.trans_le hxs)]

private lemma primitive_derivative (ell : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (lowPrimitive ell) (lowPrimitiveDerivative ell r) r := by
  have hd := ((((hasDerivAt_id r).mul (Real.hasDerivAt_log hr.ne')).add
    ((hasDerivAt_id r).const_mul (ell⁻¹ - Real.log ell - 1))).add_const
      (ell⁻¹ + ell - 1)).sub (hasDerivAt_inv hr.ne')
  have hd' : HasDerivAt (lowPrimitive ell)
      (1 * Real.log r + r * r⁻¹ + (ell⁻¹ - Real.log ell - 1) * 1 -
        (-(r ^ 2)⁻¹)) r := by
    simpa only [lowPrimitive, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, id_eq] using! hd
  apply hd'.congr_deriv
  unfold lowPrimitiveDerivative
  field_simp [hr.ne']
  <;> ring

private lemma primitive_dyadic {ell r : ℝ} (hell : 0 < ell) (hr : 0 < r) :
    lowPrimitiveDerivative ell r - (1 / 2 : ℝ) *
      lowPrimitiveDerivative ell (r + Real.log 2) = mainDerivative ell r := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn : 0 < r + Real.log 2 := by linarith
  have hnext : Real.log (1 + Real.log 2 / r) =
      Real.log (r + Real.log 2) - Real.log r := by
    rw [show 1 + Real.log 2 / r = (r + Real.log 2) / r by
      field_simp [hr.ne'] <;> ring, Real.log_div hn.ne' hr.ne']
  unfold lowPrimitiveDerivative mainDerivative
  rw [Real.log_div hr.ne' hell.ne', hnext]
  field_simp [hell.ne']
  <;> ring

private lemma dyadic_hasDerivAt {x s : ℝ} (hx : 1 < x) (hxs : x < s) :
    HasDerivAt (b x) (bDerivative x s) s := by
  have hs1 : 1 < s := hx.trans hxs
  have hs0 : 0 < s := by linarith
  have h2s : 0 < 2 * s := by positivity
  have hell : 0 < Real.log x := Real.log_pos hx
  have hr : 0 < Real.log s := Real.log_pos hs1
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : Real.log (2 * s) = Real.log s + Real.log 2 := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hs0.ne']
    ring
  have he1 := (ActualFactorialRobinHighDerivative.result.2.2 (Real.log s) hr).2.2.1
  have he2 := (ActualFactorialRobinHighDerivative.result.2.2
    (Real.log s + Real.log 2) (by linarith)).2.2.1
  have hq1 := ((primitive_derivative (Real.log x) hr).add he1).comp s
    (Real.hasDerivAt_log hs0.ne')
  have hlogDeriv : HasDerivAt (fun t : ℝ => Real.log (2 * t)) s⁻¹ s := by
    have hd : HasDerivAt (fun t : ℝ => Real.log (2 * t))
        ((2 * s)⁻¹ * (2 * 1)) s := by
      simpa only [Function.comp_def, id_eq] using!
        (Real.hasDerivAt_log h2s.ne').comp s ((hasDerivAt_id s).const_mul (2 : ℝ))
    apply hd.congr_deriv
    field_simp [hs0.ne']
    <;> ring
  have houter2 : HasDerivAt
      (fun u : ℝ => lowPrimitive (Real.log x) u + highRemainder u)
      (lowPrimitiveDerivative (Real.log x) (Real.log (2 * s)) +
        highRemainderDerivative (Real.log (2 * s))) (Real.log (2 * s)) := by
    rw [hlog2]
    exact (primitive_derivative (Real.log x) (by linarith :
      0 < Real.log s + Real.log 2)).add he2
  have hq2 := houter2.comp s hlogDeriv
  have hlocal : b x =ᶠ[𝓝 s] (fun t : ℝ =>
      (lowPrimitive (Real.log x) (Real.log t) + highRemainder (Real.log t)) -
      (1 / 2 : ℝ) * (lowPrimitive (Real.log x) (Real.log (2 * t)) +
        highRemainder (Real.log (2 * t)))) := by
    filter_upwards [Ioi_mem_nhds hxs] with t ht
    change x < t at ht
    have ht0 : 0 < t := by linarith
    have hx2t : x ≤ 2 * t := by linarith
    unfold b
    calc
      _ = t * P x t - (1 / 2 : ℝ) * ((2 * t) * P x (2 * t)) := by ring
      _ = _ := by rw [normalized_identity hx ht.le, normalized_identity hx hx2t]
  have hd := (hq1.sub (hq2.const_mul (1 / 2 : ℝ))).congr_of_eventuallyEq hlocal
  apply hd.congr_deriv
  rw [hlog2]
  unfold bDerivative
  calc
    _ = (lowPrimitiveDerivative (Real.log x) (Real.log s) -
        (1 / 2 : ℝ) * lowPrimitiveDerivative (Real.log x) (Real.log s + Real.log 2) +
        highRemainderDerivative (Real.log s) -
        (1 / 2 : ℝ) * highRemainderDerivative (Real.log s + Real.log 2)) / s := by ring
    _ = _ := by rw [primitive_dyadic hell hr]

private lemma signed_derivative_error {x s : ℝ} (hx : 1 < x) (hxs : x < s) :
    |s * bDerivative x s - mainDerivative (Real.log x) (Real.log s)| ≤
      3 * (Real.log s)⁻¹ ^ 2 + 6 * (Real.log s)⁻¹ ^ 3 := by
  have hs0 : 0 < s := by linarith
  have hr : 0 < Real.log s := Real.log_pos (hx.trans hxs)
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn : 0 < Real.log s + Real.log 2 := by linarith
  have he1 := (ActualFactorialRobinHighDerivative.result.2.2 (Real.log s) hr).2.2.2.2
  have he2 := (ActualFactorialRobinHighDerivative.result.2.2
    (Real.log s + Real.log 2) hn).2.2.2.2
  have hinv : (Real.log s + Real.log 2)⁻¹ ≤ (Real.log s)⁻¹ :=
    inv_anti₀ hr (by linarith)
  have hnumb : 2 * ((Real.log s + Real.log 2)⁻¹ ^ 2 +
      2 * (Real.log s + Real.log 2)⁻¹ ^ 3) ≤
      2 * ((Real.log s)⁻¹ ^ 2 + 2 * (Real.log s)⁻¹ ^ 3) := by gcongr
  have he2' := he2.trans hnumb
  have herror : s * bDerivative x s - mainDerivative (Real.log x) (Real.log s) =
      highRemainderDerivative (Real.log s) -
        (1 / 2 : ℝ) * highRemainderDerivative (Real.log s + Real.log 2) := by
    unfold bDerivative
    field_simp [hs0.ne']
    <;> ring
  rw [herror]
  calc
    _ ≤ |highRemainderDerivative (Real.log s)| +
      (1 / 2 : ℝ) * |highRemainderDerivative (Real.log s + Real.log 2)| := by
        simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] using
          abs_sub (highRemainderDerivative (Real.log s))
            ((1 / 2 : ℝ) * highRemainderDerivative (Real.log s + Real.log 2))
    _ ≤ 2 * ((Real.log s)⁻¹ ^ 2 + 2 * (Real.log s)⁻¹ ^ 3) +
      (1 / 2 : ℝ) * (2 * ((Real.log s)⁻¹ ^ 2 + 2 * (Real.log s)⁻¹ ^ 3)) := by
        exact add_le_add he1 (mul_le_mul_of_nonneg_left he2' (by norm_num))
    _ = _ := by ring

private lemma main_bounds {ell r : ℝ} (hell : 1 ≤ ell) (her : ell ≤ r) :
    0 ≤ mainDerivative ell r ∧ mainDerivative ell r ≤
      (1 / 2 : ℝ) * Real.log (r / ell) + 1 / (2 * ell) + r⁻¹ ^ 2 := by
  have hell0 : 0 < ell := by linarith
  have hr : 0 < r := hell0.trans_le her
  have hL : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hL1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hratio : 1 ≤ r / ell := (le_div_iff₀ hell0).mpr (by simpa using her)
  have hlogRatio : 0 ≤ Real.log (r / ell) := Real.log_nonneg hratio
  have hnextArg : 1 ≤ 1 + Real.log 2 / r :=
    le_add_of_nonneg_right (div_nonneg hL hr.le)
  have hlogNext : 0 ≤ Real.log (1 + Real.log 2 / r) := Real.log_nonneg hnextArg
  have hlogNextUpper : Real.log (1 + Real.log 2 / r) ≤ ell⁻¹ := by
    calc
      _ ≤ Real.log 2 / r := by
        simpa using Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + Real.log 2 / r)
      _ ≤ r⁻¹ := by
        simpa only [one_div] using div_le_div_of_nonneg_right hL1 hr.le
      _ ≤ ell⁻¹ := inv_anti₀ hell0 her
  have hi : (r + Real.log 2)⁻¹ ≤ r⁻¹ := inv_anti₀ hr (by linarith)
  have hisq : (r + Real.log 2)⁻¹ ^ 2 ≤ r⁻¹ ^ 2 := by gcongr
  have hn : 0 ≤ (r + Real.log 2)⁻¹ ^ 2 := sq_nonneg _
  have hhalf : 1 / (2 * ell) = (1 / 2 : ℝ) * ell⁻¹ := by ring
  unfold mainDerivative
  rw [hhalf]
  constructor <;> nlinarith [sq_nonneg r⁻¹]

private lemma complete_derivative_bound {x s : ℝ} (hx : 1 < x) (hxs : x < s)
    (hell : 1 ≤ Real.log x) :
    |s * bDerivative x s| ≤
      (1 / 2 : ℝ) * Real.log (Real.log s / Real.log x) + 21 / (2 * Real.log x) := by
  have hs0 : 0 < s := by linarith
  have hr : 0 < Real.log s := Real.log_pos (hx.trans hxs)
  have her : Real.log x ≤ Real.log s := Real.log_le_log (by linarith) hxs.le
  have hm := main_bounds hell her
  have he := signed_derivative_error hx hxs
  have hi : (Real.log s)⁻¹ ≤ (Real.log x)⁻¹ := inv_anti₀ (by linarith) her
  have hi0 : 0 ≤ (Real.log s)⁻¹ := inv_nonneg.mpr hr.le
  have hi1 : (Real.log s)⁻¹ ≤ 1 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1) (hell.trans her)
  have hisq : (Real.log s)⁻¹ ^ 2 ≤ (Real.log s)⁻¹ := by nlinarith
  have hicube : (Real.log s)⁻¹ ^ 3 ≤ (Real.log s)⁻¹ := by
    calc
      _ = (Real.log s)⁻¹ ^ 2 * (Real.log s)⁻¹ := by ring
      _ ≤ (Real.log s)⁻¹ * (Real.log s)⁻¹ := mul_le_mul_of_nonneg_right hisq hi0
      _ ≤ _ := by simpa only [← sq] using hisq
  have habs : |s * bDerivative x s| ≤ mainDerivative (Real.log x) (Real.log s) +
      |s * bDerivative x s - mainDerivative (Real.log x) (Real.log s)| := by
    have h := abs_add_le (mainDerivative (Real.log x) (Real.log s))
      (s * bDerivative x s - mainDerivative (Real.log x) (Real.log s))
    have hsum : mainDerivative (Real.log x) (Real.log s) +
        (s * bDerivative x s - mainDerivative (Real.log x) (Real.log s)) =
        s * bDerivative x s := by ring
    rw [hsum, abs_of_nonneg hm.1] at h
    exact h
  have hhalf : 21 / (2 * Real.log x) = (21 / 2 : ℝ) * (Real.log x)⁻¹ := by ring
  have hhalf1 : 1 / (2 * Real.log x) = (1 / 2 : ℝ) * (Real.log x)⁻¹ := by ring
  rw [hhalf]
  rw [hhalf1] at hm
  nlinarith [hisq.trans hi, hicube.trans hi]

/-- The same physical factorial Robin P and its dyadic growth weight have a
complete exact decomposition and a genuine derivative with a signed high-error
budget. The complete physical decomposition includes s=x, where the low interval
is empty. The displayed final bound is uniform in both x and s in its stated domain. -/
theorem result :
    (∀ x s : ℝ, 1 < x → x ≤ s →
      IntegrableOn (physicalIntegrand s) (Ioi x) ∧
      s * P x s = lowPrimitive (Real.log x) (Real.log s) + highRemainder (Real.log s)) ∧
    (∀ x s : ℝ, 1 < x → x < s →
    IntegrableOn (physicalIntegrand s) (Ioi x) ∧
    s * P x s = lowPrimitive (Real.log x) (Real.log s) + highRemainder (Real.log s) ∧
    HasDerivAt (b x) (bDerivative x s) s ∧
    |s * bDerivative x s - mainDerivative (Real.log x) (Real.log s)| ≤
      3 * (Real.log s)⁻¹ ^ 2 + 6 * (Real.log s)⁻¹ ^ 3 ∧
    (1 ≤ Real.log x → |s * bDerivative x s| ≤
      (1 / 2 : ℝ) * Real.log (Real.log s / Real.log x) + 21 / (2 * Real.log x))) := by
  constructor
  · intro x s hx hxs
    exact ⟨physical_integrable hx hxs, normalized_identity hx hxs⟩
  · intro x s hx hxs
    exact ⟨physical_integrable hx hxs.le, normalized_identity hx hxs.le,
      dyadic_hasDerivAt hx hxs, signed_derivative_error hx hxs,
      complete_derivative_bound hx hxs⟩

end D5.S3.Arith.Robin.ActualFactorialRobinDyadicDerivative

#print axioms D5.S3.Arith.Robin.ActualFactorialRobinDyadicDerivative.result

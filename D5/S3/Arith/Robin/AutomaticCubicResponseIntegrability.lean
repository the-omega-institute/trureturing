/- GID: D5/S3/Arith/Robin/AutomaticCubicResponseIntegrability
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/AutomaticCubicResponseIntegrability
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Original bounds supply ordinary integrability of both complete cubic responses. -/

/-
Purpose: prove ordinary integrability of the literal actual and cubic prime
responses on the unchanged complete selected domain from its original bounds.
The exact moving continuum center is treated by its log-log primitive.
The cubic atoms are continuous coefficients restricted by measurable clock
thresholds. Reference-kernel integrability and actual/reference transport are
reused; no prime-mass or response-integrability premise is assumed.
-/

import D5.S3.Arith.Robin.ThirdOrderPrimeKernel
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Arith.Robin.AutomaticCubicResponseIntegrability

open Set MeasureTheory
open scoped Topology
open D5.S3.Arith.Robin.ActualRobinClockCovariance
open D5.S3.Arith.Robin.OriginalFirstClockTransport
open D5.S3.Arith.Robin.DelayedAtomTransport
open D5.S3.Arith.Robin.ThirdOrderPrimeKernel

open private original_curve selected_domain_bounds domain_compact
  window_continuous original_kernel_integrable actual_eq_reference_on_domain from
  D5.S3.Arith.Robin.OriginalFirstClockTransport
open private densityD1 densityD2 activationDensity_hasDerivAt
  densityD1_hasDerivAt densityD2_hasDerivAt kernelOffset cubicOffset
  continuumExact cubicCenter from D5.S3.Arith.Robin.ThirdOrderPrimeKernel

private theorem price_shift_integral {t H : ℝ} (ht : 1 < t) (hH : 0 ≤ H) :
    (∫ u in 0..H, g (t+u)) =
      Real.log (Real.log (t+H)) - Real.log (Real.log t) := by
  have hu1 (u : ℝ) (hu : u ∈ uIcc 0 H) : 1 < t+u := by
    rw [uIcc_of_le hH] at hu
    linarith [hu.1]
  have hd (u : ℝ) (hu : u ∈ uIcc 0 H) :
      HasDerivAt (fun v : ℝ => Real.log (Real.log (t+v))) (g (t+u)) u := by
    have ht0 : t+u ≠ 0 := ne_of_gt (by linarith [hu1 u hu])
    have hl0 : Real.log (t+u) ≠ 0 := (Real.log_pos (hu1 u hu)).ne'
    have hlog := (Real.hasDerivAt_log ht0).comp u ((hasDerivAt_id u).const_add t)
    have hloglog := (Real.hasDerivAt_log hl0).comp u hlog
    exact hloglog.congr_deriv (by
      dsimp [g]
      simp only [mul_one, div_eq_mul_inv, mul_inv_rev]
      ring)
  have hi : IntervalIntegrable (fun u : ℝ => g (t+u)) volume 0 H := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    exact ((g_has_deriv_at (hu1 u hu)).continuousAt.comp
      (continuousAt_const.add continuousAt_id)).continuousWithinAt
  simpa only [add_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := 0) (b := H) (f := fun u : ℝ => Real.log (Real.log (t+u)))
      (f' := fun u : ℝ => g (t+u)) hd hi

private theorem continuumExact_closed_form {t H d : ℝ} (ht : 1 < t) (hH : 0 ≤ H) :
    continuumExact t H d =
      (Real.log (Real.log (t+H)) - Real.log (Real.log t) - H*g (t+H)) /
        (activationDensity t*d) := by
  have hi : IntervalIntegrable (fun u : ℝ => g (t+u)) volume 0 H := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [uIcc_of_le hH] at hu
    have hu1 : 1 < t+u := by linarith [hu.1]
    exact ((g_has_deriv_at hu1).continuousAt.comp
      (continuousAt_const.add continuousAt_id)).continuousWithinAt
  unfold continuumExact kernelOffset
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub hi intervalIntegrable_const,
    price_shift_integral ht hH, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]

private theorem continuumExact_continuousOn
    (X : OriginalWindow) {ell R : ℝ} (hell : 243 ≤ ell)
    (hbounds : OriginalBounds X ell R) :
    ContinuousOn (fun t => continuumExact t (windowLength t) (normalization t))
      (selectedDomain X) := by
  let S := selectedDomain X
  have hsub := selected_domain_bounds X hbounds
  have hB : Continuous (fun t : ℝ => t+windowLength t) := by
    exact continuous_id.add
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 4/5))
  have hH : Continuous windowLength :=
    Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 4/5)
  have hD : ContinuousOn (fun t => activationDensity t*normalization t) S := by
    simpa only [normalization] using (window_continuous (R := R) hell).2.mono hsub
  have hlog : ContinuousOn Real.log (Ioi (1 : ℝ)) :=
    continuousOn_id.log (fun t ht => ne_of_gt (lt_trans zero_lt_one ht))
  have hloglog : ContinuousOn (fun t : ℝ => Real.log (Real.log t)) (Ioi 1) := by
    exact hlog.log (fun t ht => (Real.log_pos ht).ne')
  have hp : ContinuousOn g (Ioi 1) := fun t ht =>
    (g_has_deriv_at ht).continuousAt.continuousWithinAt
  have hin : MapsTo (fun t : ℝ => t+windowLength t) S (Ioi 1) := by
    intro t ht
    have ht1 : 1 < t := by linarith [(hsub ht).1]
    have hH0 : 0 ≤ windowLength t := Real.rpow_nonneg (by linarith : 0 ≤ t) _
    exact show 1 < t+windowLength t from by linarith
  have htS : S ⊆ Ioi (1 : ℝ) := by
    intro t ht
    exact show 1 < t from by linarith [(hsub ht).1]
  have hclosed : ContinuousOn (fun t =>
      (Real.log (Real.log (t+windowLength t)) - Real.log (Real.log t) -
          windowLength t*g (t+windowLength t)) /
        (activationDensity t*normalization t)) S := by
    apply (((hloglog.comp hB.continuousOn hin).sub (hloglog.mono htS)).sub
      (hH.continuousOn.mul (hp.comp hB.continuousOn hin))).div hD
    intro t ht
    have ht1 : 1 < t := htS ht
    exact (mul_pos (original_curve.positive_weight t ht1)
      (Real.rpow_pos_of_pos (by linarith : 0 < t) _)).ne'
  apply hclosed.congr
  intro t ht
  exact continuumExact_closed_form (htS ht)
    (Real.rpow_nonneg (by linarith [(hsub ht).1] : 0 ≤ t) _)

private theorem cubicOffset_continuousOn
    (X : OriginalWindow) {ell R : ℝ} (hell : 243 ≤ ell)
    (hbounds : OriginalBounds X ell R) (z : ℝ) :
    ContinuousOn (fun t => cubicOffset t (windowLength t) (normalization t) (z-t))
      (selectedDomain X) := by
  have hsub := selected_domain_bounds X hbounds
  intro t ht
  have ht1 : 1 < t := by linarith [(hsub ht).1]
  have hw := (activationDensity_hasDerivAt ht1).continuousAt
  have hd1 := (densityD1_hasDerivAt ht1).continuousAt
  have hd2 := (densityD2_hasDerivAt ht1).continuousAt
  have hH : ContinuousAt windowLength t :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 4/5)).continuousAt
  have hN : ContinuousAt normalization t :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 11/10)).continuousAt
  have hu : ContinuousAt (fun x : ℝ => z-x) t := continuousAt_const.sub continuousAt_id
  have hw0 : activationDensity t ≠ 0 := (original_curve.positive_weight t ht1).ne'
  have hN0 : normalization t ≠ 0 :=
    (Real.rpow_pos_of_pos (by linarith : 0 < t) _).ne'
  have hr1 : ContinuousAt (fun x => densityD1 x/(2*activationDensity x)) t :=
    hd1.div (continuousAt_const.mul hw) (mul_ne_zero (by norm_num) hw0)
  have hr2 : ContinuousAt (fun x => densityD2 x/(6*activationDensity x)) t :=
    hd2.div (continuousAt_const.mul hw) (mul_ne_zero (by norm_num) hw0)
  simpa only [cubicOffset] using
    ((((hH.sub hu).add (hr1.mul ((hH.pow 2).sub (hu.pow 2)))).add
      (hr2.mul ((hH.pow 3).sub (hu.pow 3)))).div hN hN0).continuousWithinAt
        (s := selectedDomain X)

private theorem cubicCenter_continuousOn
    (X : OriginalWindow) {ell R : ℝ} (hell : 243 ≤ ell)
    (hbounds : OriginalBounds X ell R) :
    ContinuousOn (fun t => cubicCenter t (windowLength t) (normalization t))
      (selectedDomain X) := by
  have hsub := selected_domain_bounds X hbounds
  intro t ht
  have ht1 : 1 < t := by linarith [(hsub ht).1]
  have hw := (activationDensity_hasDerivAt ht1).continuousAt
  have hd1 := (densityD1_hasDerivAt ht1).continuousAt
  have hd2 := (densityD2_hasDerivAt ht1).continuousAt
  have hH : ContinuousAt windowLength t :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 4/5)).continuousAt
  have hN : ContinuousAt normalization t :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 11/10)).continuousAt
  have hw0 : activationDensity t ≠ 0 := (original_curve.positive_weight t ht1).ne'
  have hN0 : normalization t ≠ 0 :=
    (Real.rpow_pos_of_pos (by linarith : 0 < t) _).ne'
  have h2 : 2*normalization t ≠ 0 := mul_ne_zero (by norm_num) hN0
  have h3 : 3*activationDensity t*normalization t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hw0) hN0
  have h8 : 8*activationDensity t*normalization t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hw0) hN0
  simpa only [cubicCenter] using
    ((((hH.pow 2).div (continuousAt_const.mul hN) h2).add
      ((hd1.mul (hH.pow 3)).div ((continuousAt_const.mul hw).mul hN) h3)).add
        ((hd2.mul (hH.pow 4)).div ((continuousAt_const.mul hw).mul hN) h8)).continuousWithinAt
          (s := selectedDomain X)

private theorem actual_atom_integrable
    (X : OriginalWindow) {ell R : ℝ} (hell : 243 ≤ ell)
    (hbounds : OriginalBounds X ell R) {q : ℕ} (hq : q.Prime) :
    IntegrableOn (fun t => Real.log q * actualKernel g t (t+windowLength t)
      (activationDensity t*normalization t) (firstClock q)) (selectedDomain X) := by
  have href : IntegrableOn (fun t => Real.log q * referenceKernel g t (t+windowLength t)
      (activationDensity t*normalization t) (firstClock q)) (selectedDomain X) := by
    simpa only [windowLength, normalization] using
      (original_kernel_integrable X hell hbounds (firstClock q)).const_mul (Real.log q)
  apply href.congr
  filter_upwards [ae_restrict_mem (domain_compact X).measurableSet] with t ht
  have he : actualKernel g t (t+windowLength t)
        (activationDensity t*normalization t) (firstClock q) =
      referenceKernel g t (t+windowLength t)
        (activationDensity t*normalization t) (firstClock q) := by
    simpa only [windowLength, normalization] using
      actual_eq_reference_on_domain X hell hbounds hq ht
  exact congrArg (fun y : ℝ => Real.log q*y) he.symm

private theorem cubic_atom_integrable
    (X : OriginalWindow) {ell R : ℝ} (hell : 243 ≤ ell)
    (hbounds : OriginalBounds X ell R) (q : ℕ) :
    IntegrableOn (fun t =>
      if t < firstClock q ∧ firstClock q ≤ t+windowLength t then
        Real.log q*cubicOffset t (windowLength t) (normalization t) (firstClock q-t)
      else 0) (selectedDomain X) := by
  have hc := (cubicOffset_continuousOn X hell hbounds (firstClock q)).const_mul (Real.log q)
  have hi := hc.integrableOn_compact (domain_compact X)
  have hB : Continuous (fun t : ℝ => t+windowLength t) :=
    continuous_id.add (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 4/5))
  have hm : MeasurableSet {t : ℝ | t < firstClock q ∧ firstClock q ≤ t+windowLength t} :=
    MeasurableSet.inter measurableSet_Iio
      (measurableSet_le (measurable_const : Measurable (fun _ : ℝ => firstClock q)) hB.measurable)
  simpa only [Set.indicator, Set.mem_setOf_eq] using hi.indicator hm

/-- Both ordinary response integrability premises follow from the unchanged
complete selected domain and its original bounds. No GM mass or response
estimate is assumed here. -/
theorem complete_selected_responses_integrable
    (X : OriginalWindow) {ell R : ℝ} (hell : 243 ≤ ell)
    (hbounds : OriginalBounds X ell R) :
    IntegrableOn (fun t =>
      canonicalActualPrimeResponse R t (windowLength t) (normalization t)) (selectedDomain X) ∧
    IntegrableOn (fun t =>
      cubicPrimeResponse R t (windowLength t) (normalization t)) (selectedDomain X) := by
  have hcont := (continuumExact_continuousOn X hell hbounds).integrableOn_compact
    (domain_compact X)
  have hcenter := (cubicCenter_continuousOn X hell hbounds).integrableOn_compact
    (domain_compact X)
  constructor
  · have hsum : IntegrableOn (fun t => ∑ q ∈ Nat.primesLE ⌊2*R⌋₊,
        Real.log q*actualKernel g t (t+windowLength t)
          (activationDensity t*normalization t) (firstClock q)) (selectedDomain X) :=
      integrable_finsetSum (Nat.primesLE ⌊2*R⌋₊)
        (fun q hq => actual_atom_integrable X hell hbounds (Nat.mem_primesLE.mp hq).2)
    exact hsum.sub hcont
  · have hsum : IntegrableOn (fun t => ∑ q ∈ Nat.primesLE ⌊2*R⌋₊,
        if t < firstClock q ∧ firstClock q ≤ t+windowLength t then
          Real.log q*cubicOffset t (windowLength t) (normalization t) (firstClock q-t)
        else 0) (selectedDomain X) :=
      integrable_finsetSum (Nat.primesLE ⌊2*R⌋₊)
        (fun q _ => cubic_atom_integrable X hell hbounds q)
    have heq (t : ℝ) : cubicPrimeResponse R t (windowLength t) (normalization t) =
        (∑ q ∈ Nat.primesLE ⌊2*R⌋₊,
          if t < firstClock q ∧ firstClock q ≤ t+windowLength t then
            Real.log q*cubicOffset t (windowLength t) (normalization t) (firstClock q-t)
          else 0) - cubicCenter t (windowLength t) (normalization t) := by
      unfold cubicPrimeResponse actualPrimes
      rw [Finset.sum_filter]
    exact (hsum.sub hcenter).congr (Filter.Eventually.of_forall fun t => (heq t).symm)

#print axioms complete_selected_responses_integrable

end D5.S3.Arith.Robin.AutomaticCubicResponseIntegrability

end

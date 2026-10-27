/- GID: D5/S3/Arith/Robin/CompleteCubicError
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/CompleteCubicError
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Elementary integer counting gives vanishing complete-window cubic error without a GM premise. -/

/- The actual original first-clock exclusion, elementary integer counting,
logarithm absorption and automatic integrability supply a replacement-error
bound on the complete unchanged selected domain. No favorable signed prime
moment, fixed kappa estimate, EL.14 or RH conclusion is supplied. -/

import D5.S3.Arith.Robin.AutomaticCubicResponseIntegrability
import Mathlib.Order.Interval.Finset.Nat
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Arith.Robin.CompleteCubicError

open Set MeasureTheory
open scoped Topology
open D5.S3.Arith.Robin.ActualRobinClockCovariance
open D5.S3.Arith.Robin.OriginalFirstClockTransport
open D5.S3.Arith.Robin.ThirdOrderPrimeKernel

open private first_clock_spec selected_domain_bounds domain_compact from
  D5.S3.Arith.Robin.OriginalFirstClockTransport
open private selected_firstClock_initial kernelOffset cubicOffset continuumExact
  cubicCenter actualPrimeResponse canonical_actual_response_eq
  cubic_kernel_uniform_error cubic_continuum_error continuumCubic_closed_form
  cubic_scale_identity from D5.S3.Arith.Robin.ThirdOrderPrimeKernel

private theorem active_prime_interval
    (X : OriginalWindow) {ell R t H : ℝ} (hell : 243 ≤ ell)
    (hbounds : OriginalBounds X ell R) (ht : t ∈ selectedDomain X)
    {q : ℕ} (hq : q ∈ actualPrimes R t H) :
    t < (q : ℝ) ∧ (q : ℝ) ≤ t+H := by
  have hp := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).2
  have hc := (Finset.mem_filter.mp hq).2
  exact ⟨(selected_firstClock_initial X hell hbounds ht hp).2 hc.1,
    (first_clock_spec hp).1.le.trans hc.2⟩

private theorem active_prime_card_le
    (X : OriginalWindow) {ell R t H : ℝ} (hell : 243 ≤ ell)
    (hbounds : OriginalBounds X ell R) (ht : t ∈ selectedDomain X) (hH : 0 ≤ H) :
    ((actualPrimes R t H).card : ℝ) ≤ H+1 := by
  have ht0 : 0 ≤ t := by linarith [(selected_domain_bounds X hbounds ht).1]
  have hfloor : ⌊t⌋₊ ≤ ⌊t+H⌋₊ := Nat.floor_mono (by linarith)
  have hsub : actualPrimes R t H ⊆ Finset.Ioc ⌊t⌋₊ ⌊t+H⌋₊ := by
    intro q hq
    have hqI := active_prime_interval X hell hbounds ht hq
    apply Finset.mem_Ioc.mpr
    constructor
    · exact_mod_cast (Nat.floor_le ht0).trans_lt hqI.1
    · exact Nat.le_floor hqI.2
  have hcard : (actualPrimes R t H).card ≤ ⌊t+H⌋₊ - ⌊t⌋₊ := by
    simpa only [Nat.card_Ioc] using Finset.card_le_card hsub
  have hcardR : ((actualPrimes R t H).card : ℝ) ≤
      ((⌊t+H⌋₊ - ⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast hcard
  rw [Nat.cast_sub hfloor] at hcardR
  have htop : (⌊t+H⌋₊ : ℝ) ≤ t+H := Nat.floor_le (show 0 ≤ t+H from by linarith)
  have hbottom : t < (⌊t⌋₊ : ℝ)+1 := Nat.lt_floor_add_one t
  linarith

private theorem elementary_active_prime_logmass
    (X : OriginalWindow) {ell R t : ℝ} (hell : 243 ≤ ell)
    (hbounds : OriginalBounds X ell R) (ht : t ∈ selectedDomain X) :
    (∑ q ∈ actualPrimes R t (windowLength t), Real.log q) ≤
      2*windowLength t*Real.log (2*t) := by
  have ht3 : 3 ≤ t := by linarith [(selected_domain_bounds X hbounds ht).1]
  have ht1 : 1 ≤ t := by linarith
  have hH1 : 1 ≤ windowLength t := Real.one_le_rpow ht1 (by norm_num)
  have hHt : windowLength t ≤ t := Real.rpow_le_self_of_one_le ht1 (by norm_num)
  have hcard : ((actualPrimes R t (windowLength t)).card : ℝ) ≤ 2*windowLength t := by
    have hc := active_prime_card_le X hell hbounds ht (by linarith : 0 ≤ windowLength t)
    linarith
  have hlog0 : 0 ≤ Real.log (2*t) := Real.log_nonneg (by linarith)
  calc
    _ ≤ ∑ _q ∈ actualPrimes R t (windowLength t), Real.log (2*t) := by
      apply Finset.sum_le_sum
      intro q hq
      have hp := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).2
      have hqI := active_prime_interval X hell hbounds ht hq
      exact Real.log_le_log (by exact_mod_cast hp.pos) (by linarith [hqI.2])
    _ = ((actualPrimes R t (windowLength t)).card : ℝ)*Real.log (2*t) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2*windowLength t)*Real.log (2*t) :=
      mul_le_mul_of_nonneg_right hcard hlog0

private theorem log_two_mul_le_rpow {t : ℝ} (ht : 3 ≤ t) :
    Real.log (2*t) ≤ 21*t^(1/20 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hp : 1 ≤ t^(1/20 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hl : Real.log t ≤ 20*t^(1/20 : ℝ) := by
    convert Real.log_le_rpow_div (x := t) (ε := 1/20) ht0.le (by norm_num) using 1 <;> ring
  have hl2 : Real.log (2 : ℝ) ≤ 1 := by
    simpa only [show (2 : ℝ)-1=1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [Real.log_mul (by norm_num) ht0.ne']
  linarith

private theorem actual_prime_error_of_logmass
    {R t H d L : ℝ} (ht : 3 ≤ t) (hH : 0 ≤ H) (hd : 0 < d)
    (hmass : (∑ q ∈ actualPrimes R t H, Real.log q) ≤ 2*H*L) :
    |actualPrimeResponse R t H d - cubicPrimeResponse R t H d| ≤
      (19*L+38/5) * H^5 / (t^3*d) := by
  have ht0 : 0 < t := by linarith
  let A : ℝ := (19/2 : ℝ)*H^4/(t^3*d)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsum : |∑ q ∈ actualPrimes R t H, Real.log q *
      (kernelOffset t H d (firstClock q-t)-cubicOffset t H d (firstClock q-t))| ≤
        19*L*H^5/(t^3*d) := by
    calc
      _ ≤ ∑ q ∈ actualPrimes R t H, |Real.log q *
          (kernelOffset t H d (firstClock q-t)-cubicOffset t H d (firstClock q-t))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ actualPrimes R t H, Real.log q*A := by
        apply Finset.sum_le_sum
        intro q hq
        have hc := (Finset.mem_filter.mp hq).2
        have hu : firstClock q-t ∈ Icc 0 H := ⟨by linarith [hc.1], by linarith [hc.2]⟩
        rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg q)]
        exact mul_le_mul_of_nonneg_left (cubic_kernel_uniform_error ht hH hd hu)
          (Real.log_natCast_nonneg q)
      _ = (∑ q ∈ actualPrimes R t H, Real.log q)*A := by rw [Finset.sum_mul]
      _ ≤ (2*H*L)*A := mul_le_mul_of_nonneg_right hmass hA
      _ = 19*L*H^5/(t^3*d) := by dsimp [A]; ring
  have hcont := cubic_continuum_error ht hH hd
  rw [continuumCubic_closed_form] at hcont
  have heq : actualPrimeResponse R t H d-cubicPrimeResponse R t H d =
      (∑ q ∈ actualPrimes R t H, Real.log q *
        (kernelOffset t H d (firstClock q-t)-cubicOffset t H d (firstClock q-t))) -
      (continuumExact t H d-cubicCenter t H d) := by
    unfold actualPrimeResponse cubicPrimeResponse
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    _ ≤ |∑ q ∈ actualPrimes R t H, Real.log q *
        (kernelOffset t H d (firstClock q-t)-cubicOffset t H d (firstClock q-t))| +
        |continuumExact t H d-cubicCenter t H d| := abs_sub _ _
    _ ≤ 19*L*H^5/(t^3*d)+(38/5 : ℝ)*H^5/(t^3*d) := add_le_add hsum hcont
    _ = _ := by ring

private theorem complete_selected_pointwise_error
    (X : OriginalWindow) {ell R t : ℝ} (hell : 243 ≤ ell)
    (hbounds : OriginalBounds X ell R) (ht : t ∈ selectedDomain X) :
    |canonicalActualPrimeResponse R t (windowLength t) (normalization t) -
      cubicPrimeResponse R t (windowLength t) (normalization t)| ≤
        408*t^(-1/20 : ℝ) := by
  have ht3 : 3 ≤ t := by linarith [(selected_domain_bounds X hbounds ht).1]
  have ht0 : 0 < t := by linarith
  have hs := actual_prime_error_of_logmass (R := R) (t := t)
    (H := windowLength t) (d := normalization t) (L := Real.log (2*t))
    ht3 (Real.rpow_nonneg ht0.le _)
    (Real.rpow_pos_of_pos ht0 _) (elementary_active_prime_logmass X hell hbounds ht)
  have hs' : |actualPrimeResponse R t (windowLength t) (normalization t) -
      cubicPrimeResponse R t (windowLength t) (normalization t)| ≤
        (19*Real.log (2*t)+38/5)*t^(-1/10 : ℝ) := by
    simpa only [mul_div_assoc, cubic_scale_identity ht0] using hs
  have hcoeff : 19*Real.log (2*t)+38/5 ≤ (399+38/5 : ℝ)*t^(1/20 : ℝ) := by
    have hl := log_two_mul_le_rpow ht3
    have h1 : 1 ≤ t^(1/20 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    nlinarith
  have hpower : t^(1/20 : ℝ)*t^(-1/10 : ℝ) = t^(-1/20 : ℝ) := by
    rw [← Real.rpow_add ht0]
    norm_num
  rw [canonical_actual_response_eq X hell hbounds ht]
  calc
    _ ≤ (19*Real.log (2*t)+38/5)*t^(-1/10 : ℝ) := hs'
    _ ≤ ((399+38/5 : ℝ)*t^(1/20 : ℝ))*t^(-1/10 : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg ht0.le _)
    _ = (399+38/5 : ℝ)*t^(-1/20 : ℝ) := by rw [mul_assoc, hpower]
    _ ≤ 408*t^(-1/20 : ℝ) :=
      mul_le_mul_of_nonneg_right (by norm_num : (399+38/5 : ℝ) ≤ 408)
        (Real.rpow_nonneg ht0.le _)

/-- The literal complete-family cubic replacement error tends to zero per
unit selected volume with no prime-distribution or integrability premise.
Every original selected edge and the strict actual initial endpoint remain. -/
theorem complete_selected_cubic_error
    (X : OriginalWindow) {ell R : ℝ} (hell : 243 ≤ ell)
    (hbounds : OriginalBounds X ell R) :
    |(∫ t in selectedDomain X,
        canonicalActualPrimeResponse R t (windowLength t) (normalization t)) -
      (∫ t in selectedDomain X,
        cubicPrimeResponse R t (windowLength t) (normalization t))| ≤
      408*ell^(-1/20 : ℝ)*volume.real (selectedDomain X) := by
  obtain ⟨hactual, hcubic⟩ :=
    D5.S3.Arith.Robin.AutomaticCubicResponseIntegrability.complete_selected_responses_integrable
      X hell hbounds
  have hsub := selected_domain_bounds X hbounds
  have hmeas : MeasurableSet (selectedDomain X) := (domain_compact X).measurableSet
  let : IsFiniteMeasure (volume.restrict (selectedDomain X)) :=
    ⟨by simpa using (domain_compact X).measure_lt_top⟩
  have hpoint : ∀ t ∈ selectedDomain X,
      ‖canonicalActualPrimeResponse R t (windowLength t) (normalization t) -
        cubicPrimeResponse R t (windowLength t) (normalization t)‖ ≤
          408*ell^(-1/20 : ℝ) := by
    intro t ht
    have hs := complete_selected_pointwise_error X hell hbounds ht
    have hpow : t^(-1/20 : ℝ) ≤ ell^(-1/20 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (hsub ht).1 (by norm_num)
    simpa only [Real.norm_eq_abs] using hs.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
  rw [← integral_sub hactual hcubic]
  have hn := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := volume.restrict (selectedDomain X))
    ((ae_restrict_iff' hmeas).mpr (Filter.Eventually.of_forall hpoint))
  simpa only [Real.norm_eq_abs, measureReal_restrict_apply_univ, mul_assoc] using hn

#print axioms complete_selected_cubic_error

end D5.S3.Arith.Robin.CompleteCubicError

end

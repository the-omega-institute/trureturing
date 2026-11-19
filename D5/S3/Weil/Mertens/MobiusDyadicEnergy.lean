/- GID: D5/S3/Weil/Mertens/MobiusDyadicEnergy
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/MobiusDyadicEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An actual zeta zero forces cumulative signed Möbius shell energy growth. -/

import D5.S3.Weil.Mertens.MobiusDyadicEnergy.FiniteResponse
import Batteries.Tactic.OpenPrivate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.MobiusDyadicEnergy

open Set MeasureTheory Filter
open scoped Topology Convolution BigOperators NNReal ENNReal

open D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence (mobiusPartialSum)
open D5.S3.Arith.MoebiusLogarithmic

/-- The exact signed difference of the weighted Möbius sum at x and 2x. -/
def mobiusDyadicDifference (x : ℝ) : ℝ :=
  mobiusPartialSum x - mobiusPartialSum (2 * x)

/-- The squared signed difference integrated over the dyadic shell. -/
def mobiusDyadicShellEnergy (k : ℕ) : ℝ :=
  ∫ x in Ioc ((2 : ℝ) ^ k) (2 ^ (k + 1)), mobiusDyadicDifference x ^ 2

/-- The exponential energy of a zero of real part β on a logarithmic prefix. -/
def K (β U : ℝ) : ℝ := ∫ t in (0 : ℝ)..U, Real.exp ((2 * β - 1) * t)

open private MobiusCausalKernel.h from D5.S3.Weil.Mertens.MobiusDyadicEnergy.Kernel
open private CausalResolventL1.norm_q_le q causal response explicitOutput
  hC hC_measurable hC_local_bound q_measurable q_local_bound
  bounded_interval cut_prefix_transfer response_integrable_and_eq
  lambda rho_ne_zero lead lead_norm_sq affine_exp_integral
  cut_bound aC_measurable aC_envelope lambda_re_nonneg actual_zero
  affineExpPrimitive affineExpPrimitive_deriv
  from D5.S3.Weil.Mertens.MobiusDyadicEnergy.FiniteResponse

private def dyadicShift : ℝ := Real.log 2
private def dyadicWeight : ℝ := Real.exp (-dyadicShift / 2)

/-- The literal real signed profile. Only its values on the nonnegative time
axis are used. The Young argument extends its finite restriction by zero. -/
private def signedProfile (t : ℝ) : ℝ :=
  MobiusCausalKernel.h t - dyadicWeight * MobiusCausalKernel.h (t + dyadicShift)

private def signedEnergy (U : ℝ) : ℝ := ∫ t in (0 : ℝ)..U, signedProfile t ^ 2

private abbrev signedC (t : ℝ) : ℂ := (signedProfile t : ℂ)

/-- The initial dyadic interval with its literal closed-interval values. -/
private def initialProfile : ℝ → ℂ := (Icc 0 dyadicShift).indicator hC

private def signedResponse (rho : ℂ) (t : ℝ) : ℂ := causal (q rho) signedC t

private lemma dyadicShift_pos : 0 < dyadicShift := Real.log_pos (by norm_num)

private lemma exp_neg_dyadicShift : Real.exp (-dyadicShift) = 1 / 2 := by
  have he : Real.exp dyadicShift = 2 := Real.exp_log (by norm_num)
  rw [Real.exp_neg, he, one_div]

private lemma signedC_eq (t : ℝ) :
    signedC t = hC t - (dyadicWeight : ℂ) * hC (t + dyadicShift) := by
  simp only [signedC, signedProfile, Complex.ofReal_sub, Complex.ofReal_mul]

private lemma signedC_measurable : Measurable signedC := by
  have hm : Measurable MobiusCausalKernel.h := by
    simpa only [Function.comp_def, hC, Complex.ofReal_re] using
      Complex.continuous_re.measurable.comp hC_measurable
  exact Complex.continuous_ofReal.measurable.comp
    (hm.sub (measurable_const.mul (hm.comp (measurable_add_const dyadicShift))))

private lemma signedC_local_bound {U t : ℝ} (ht : t ∈ Icc 0 U) :
    ‖signedC t‖ ≤ Real.exp (U / 2) + dyadicWeight * Real.exp ((U + dyadicShift) / 2) := by
  have ha : 0 < dyadicWeight := Real.exp_pos _
  have hs : t + dyadicShift ∈ Icc 0 (U + dyadicShift) :=
    ⟨add_nonneg ht.1 dyadicShift_pos.le, by linarith [ht.2]⟩
  rw [signedC_eq]
  refine (norm_sub_le _ _).trans (add_le_add (hC_local_bound ht) ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  exact mul_le_mul_of_nonneg_left (hC_local_bound hs) ha.le

private lemma initial_integrand_interval {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) (hz : riemannZeta rho = 0) {s : ℝ} (hs : 0 ≤ s) :
    IntervalIntegrable (fun u => q rho u * initialProfile (s-u)) volume 0 s := by
  have hm : Measurable initialProfile := hC_measurable.indicator measurableSet_Icc
  apply bounded_interval ((q_measurable hh).mul (hm.comp (measurable_const.sub measurable_id)))
    hs (M := (2*s+6)*Real.exp (dyadicShift/2))
  intro u hu
  change ‖q rho u * initialProfile (s-u)‖ ≤ _
  rw [norm_mul]
  have hb : ‖initialProfile (s-u)‖ ≤ Real.exp (dyadicShift/2) :=
    cut_bound (f := hC) (T := dyadicShift) (Real.exp_pos _).le
      (fun _ hv => hC_local_bound hv) (s-u)
  exact mul_le_mul (q_local_bound hh hl hz hu) hb (norm_nonneg _) (by linarith)

private lemma initial_response_eq_tail {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) (hz : riemannZeta rho = 0) {t : ℝ} (ht : 0 ≤ t) :
    causal (q rho) initialProfile (t + dyadicShift) =
      ∫ u in t..(t + dyadicShift), q rho u * hC (t + dyadicShift - u) := by
  have hts : t ≤ t + dyadicShift := by linarith [dyadicShift_pos]
  have hs : 0 ≤ t + dyadicShift := ht.trans hts
  have hi := initial_integrand_interval hh hl hz hs
  have iL : IntervalIntegrable (fun u => q rho u * initialProfile (t + dyadicShift - u))
      volume 0 t := hi.mono_set (by
    rw [uIcc_of_le ht, uIcc_of_le hs]
    exact Icc_subset_Icc le_rfl hts)
  have iR : IntervalIntegrable (fun u => q rho u * initialProfile (t + dyadicShift - u))
      volume t (t + dyadicShift) := hi.mono_set (by
    rw [uIcc_of_le hts, uIcc_of_le hs]
    exact Icc_subset_Icc ht le_rfl)
  rw [causal, ← intervalIntegral.integral_add_adjacent_intervals iL iR]
  have hleft :
      (∫ u in (0 : ℝ)..t, q rho u * initialProfile (t + dyadicShift - u)) = 0 := by
    calc
      _ = ∫ _u in (0 : ℝ)..t, (0 : ℂ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht
        intro u hu
        dsimp only
        rw [initialProfile, indicator_of_notMem (show t + dyadicShift - u ∉ Icc 0 dyadicShift
          from fun hv => (not_lt_of_ge hv.2) (by linarith [hu.2])), mul_zero]
      _ = 0 := by simp
  rw [hleft, zero_add]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hts] at hu
  dsimp only
  rw [initialProfile, indicator_of_mem (show t + dyadicShift - u ∈ Icc 0 dyadicShift by
    constructor <;> linarith [hu.1, hu.2])]

/-- The exact finite signed response, with integrability of the two new
convolution integrands. The cutoff contributes the omitted terminal interval. -/
private theorem signed_response_integrable_and_eq {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) (hz : riemannZeta rho = 0) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun u => q rho u * signedC (t-u)) volume 0 t ∧
    IntervalIntegrable (fun u => q rho u * initialProfile (t + dyadicShift - u))
      volume 0 (t + dyadicShift) ∧
    signedResponse rho t = explicitOutput rho t -
      (dyadicWeight : ℂ) * explicitOutput rho (t + dyadicShift) +
      (dyadicWeight : ℂ) * causal (q rho) initialProfile (t + dyadicShift) := by
  have hts : t ≤ t + dyadicShift := by linarith [dyadicShift_pos]
  have hs : 0 ≤ t + dyadicShift := ht.trans hts
  obtain ⟨ih, eh⟩ := response_integrable_and_eq hh hl hz ht
  obtain ⟨ishift, eshift⟩ := response_integrable_and_eq hh hl hz hs
  let g : ℝ → ℂ := fun u => q rho u * hC (t + dyadicShift - u)
  have iL : IntervalIntegrable g volume 0 t := ishift.mono_set (by
    rw [uIcc_of_le ht, uIcc_of_le hs]
    exact Icc_subset_Icc le_rfl hts)
  have iR : IntervalIntegrable g volume t (t + dyadicShift) := ishift.mono_set (by
    rw [uIcc_of_le hts, uIcc_of_le hs]
    exact Icc_subset_Icc ht le_rfl)
  have hpoint (u : ℝ) : q rho u * signedC (t-u) =
      q rho u * hC (t-u) - (dyadicWeight : ℂ) * g u := by
    rw [signedC_eq, show t-u+dyadicShift = t+dyadicShift-u by ring]
    dsimp only [g]
    ring
  have hsplit : (∫ u in (0 : ℝ)..t, g u) +
      causal (q rho) initialProfile (t + dyadicShift) = response rho (t + dyadicShift) := by
    rw [initial_response_eq_tail hh hl hz ht]
    exact intervalIntegral.integral_add_adjacent_intervals iL iR
  refine ⟨(ih.sub (iL.const_mul (dyadicWeight : ℂ))).congr (fun u _ => (hpoint u).symm),
    initial_integrand_interval hh hl hz hs, ?_⟩
  calc
    signedResponse rho t =
        ∫ u in (0 : ℝ)..t, q rho u * hC (t-u) - (dyadicWeight : ℂ) * g u :=
      intervalIntegral.integral_congr (fun u _ => hpoint u)
    _ = response rho t - (dyadicWeight : ℂ) * (∫ u in (0 : ℝ)..t, g u) := by
      rw [intervalIntegral.integral_sub ih (iL.const_mul (dyadicWeight : ℂ)),
        intervalIntegral.integral_const_mul] <;> rfl
    _ = _ := by
      rw [← eh, ← eshift, ← hsplit]
      ring

/-- The same finite-prefix Young estimate with the actual signed input. -/
private theorem signed_prefix_transfer {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) (hz : riemannZeta rho = 0) {U : ℝ} (hU : 0 ≤ U) :
    IntervalIntegrable (fun t => ‖signedResponse rho t‖^2) volume 0 U ∧
    IntervalIntegrable (fun t => signedProfile t ^ 2) volume 0 U ∧
    (∫ t in (0 : ℝ)..U, ‖signedResponse rho t‖^2) ≤ 400 * signedEnergy U := by
  have h := cut_prefix_transfer hh hl hz hU signedC_measurable
    (fun _ ht => signedC_local_bound ht)
  have hsq (t : ℝ) : ‖signedC t‖^2 = signedProfile t ^ 2 := by
    change ‖(signedProfile t : ℂ)‖^2 = _
    simp
  have hm : Measurable signedProfile := by
    simpa only [Function.comp_def, signedC, Complex.ofReal_re] using
      Complex.continuous_re.measurable.comp signedC_measurable
  have hi : IntervalIntegrable (fun t => signedProfile t ^ 2) volume 0 U := by
    apply bounded_interval (hm.pow_const 2) hU
      (M := (Real.exp (U/2) + dyadicWeight * Real.exp ((U+dyadicShift)/2))^2)
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← hsq]
    exact pow_le_pow_left₀ (norm_nonneg _) (signedC_local_bound ht) 2
  exact ⟨h.1, hi, by simpa only [signedResponse, signedEnergy, hsq] using h.2⟩

/-- The exact first two moments on one dyadic interval, combined with the
coefficients in the resolvent envelope. -/
private lemma dyadic_envelope_integral (t : ℝ) :
    (∫ v in (0 : ℝ)..dyadicShift, (2*t+6+2*v)*Real.exp (-v)) =
      t+4-dyadicShift := by
  have hi : IntervalIntegrable (fun v : ℝ => (2*t+6+2*v)*Real.exp (-v))
      volume 0 dyadicShift :=
    (by fun_prop : Continuous (fun v : ℝ => (2*t+6+2*v)*Real.exp (-v))).intervalIntegrable _ _
  have hd (v : ℝ) : HasDerivAt (affineExpPrimitive 1 (2*t+6) 2)
      ((2*t+6+2*v)*Real.exp (-v)) v := by
    simpa only [neg_one_mul] using
      affineExpPrimitive_deriv (d := 1) (by norm_num) (2*t+6) 2 v
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v) hi]
  simp only [affineExpPrimitive, one_pow, div_one, neg_one_mul, exp_neg_dyadicShift,
    neg_zero, Real.exp_zero, mul_one]
  ring

/-- The correction uses the actual envelope (2u+6)exp(-u/2) for q. -/
private lemma initial_response_bound {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) (hz : riemannZeta rho = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖(dyadicWeight : ℂ) * causal (q rho) initialProfile (t + dyadicShift)‖ ≤
      (t+4-dyadicShift)*Real.exp (-t/2) := by
  have hts : t ≤ t + dyadicShift := by linarith [dyadicShift_pos]
  let g : ℝ → ℂ := fun u => q rho u * hC (t + dyadicShift - u)
  have iTail : IntervalIntegrable g volume t (t + dyadicShift) :=
    (response_integrable_and_eq hh hl hz (ht.trans hts)).1.mono_set (by
      rw [uIcc_of_le hts, uIcc_of_le (ht.trans hts)]
      exact Icc_subset_Icc ht le_rfl)
  let f : ℝ → ℂ := fun v => (dyadicWeight : ℂ) * (q rho (t+v) * hC (dyadicShift-v))
  have ifinite : IntervalIntegrable f volume 0 dyadicShift := by
    have iShift : IntervalIntegrable (fun v => g (t+v)) volume 0 dyadicShift := by
      simpa only [sub_self, add_sub_cancel_left] using iTail.comp_add_left t
    apply (iShift.const_mul (dyadicWeight : ℂ)).congr
    intro v _
    change (dyadicWeight : ℂ) * (q rho (t+v) * hC (t+dyadicShift-(t+v))) = _
    rw [show t+dyadicShift-(t+v) = dyadicShift-v by ring] <;> rfl
  have hs : (dyadicWeight : ℂ) * causal (q rho) initialProfile (t+dyadicShift) =
      ∫ v in (0 : ℝ)..dyadicShift, f v := by
    rw [initial_response_eq_tail hh hl hz ht]
    change (dyadicWeight : ℂ) * (∫ u in t..(t+dyadicShift), g u) = _
    rw [← intervalIntegral.integral_const_mul]
    calc
      _ = ∫ v in (0 : ℝ)..dyadicShift, (dyadicWeight : ℂ) * g (t+v) := by
        symm
        simpa only [add_zero] using intervalIntegral.integral_comp_add_left
          (fun u : ℝ => (dyadicWeight : ℂ) * g u) t (a := (0 : ℝ)) (b := dyadicShift)
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro v _
        dsimp only [f, g]
        rw [show t+dyadicShift-(t+v) = dyadicShift-v by ring]
  let env : ℝ → ℝ := fun v => Real.exp (-t/2) * ((2*t+6+2*v)*Real.exp (-v))
  have ie : IntervalIntegrable env volume 0 dyadicShift :=
    (by unfold env; fun_prop : Continuous env).intervalIntegrable _ _
  have hpoint (v : ℝ) (hv : v ∈ Icc 0 dyadicShift) : ‖f v‖ ≤ env v := by
    have htv : 0 ≤ t+v := add_nonneg ht hv.1
    have hvT : 0 ≤ dyadicShift-v := sub_nonneg.mpr hv.2
    have hq : ‖q rho (t+v)‖ ≤ (2*(t+v)+6)*Real.exp (-(t+v)/2) :=
      CausalResolventL1.norm_q_le aC_measurable aC_envelope
        (lambda_re_nonneg hh) (actual_zero hh hl hz) htv
    have hh₀ : ‖hC (dyadicShift-v)‖ ≤ Real.exp ((dyadicShift-v)/2) :=
      hC_local_bound ⟨hvT, le_rfl⟩
    have ha : 0 < dyadicWeight := Real.exp_pos _
    dsimp only [f]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    calc
      _ ≤ dyadicWeight * (((2*(t+v)+6)*Real.exp (-(t+v)/2)) *
          Real.exp ((dyadicShift-v)/2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hq hh₀ (norm_nonneg _)
            (mul_nonneg (by linarith [htv]) (Real.exp_pos _).le)) ha.le
      _ = env v := by
        unfold env dyadicWeight
        rw [show Real.exp (-dyadicShift/2) *
            (((2*(t+v)+6)*Real.exp (-(t+v)/2))*Real.exp ((dyadicShift-v)/2)) =
            (2*(t+v)+6) * ((Real.exp (-dyadicShift/2)*Real.exp (-(t+v)/2)) *
              Real.exp ((dyadicShift-v)/2)) by ring,
          ← Real.exp_add, ← Real.exp_add,
          show -dyadicShift/2 + -(t+v)/2 + (dyadicShift-v)/2 = -t/2 + -v by ring,
          Real.exp_add]
        ring
  rw [hs]
  calc
    _ ≤ ∫ v in (0 : ℝ)..dyadicShift, ‖f v‖ :=
      intervalIntegral.norm_integral_le_integral_norm dyadicShift_pos.le
    _ ≤ ∫ v in (0 : ℝ)..dyadicShift, env v :=
      intervalIntegral.integral_mono_on dyadicShift_pos.le ifinite.norm ie hpoint
    _ = _ := by
      unfold env
      rw [intervalIntegral.integral_const_mul, dyadic_envelope_integral]
      ring

/-- This is (1 - 2^(rho-1))/rho^2 with the positive-base exponential convention. -/
private def signedAmplitude (rho : ℂ) : ℂ :=
  (1 - Complex.exp ((rho-1) * (dyadicShift : ℂ))) / rho^2

private def shiftedDecay (rho : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(t : ℂ)/2) * (rho * ((dyadicShift : ℂ) - (t : ℂ)) - 1) / (2*rho^2)

private def signedRemainder (rho : ℂ) (t : ℝ) : ℂ :=
  shiftedDecay rho t + (dyadicWeight : ℂ) * causal (q rho) initialProfile (t+dyadicShift)

private lemma signed_response_split {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) (hz : riemannZeta rho = 0) {t : ℝ} (ht : 0 ≤ t) :
    signedResponse rho t = signedAmplitude rho * lead rho t + signedRemainder rho t := by
  have ha : (dyadicWeight : ℂ) = Complex.exp (-(dyadicShift : ℂ)/2) := by
    simp only [dyadicWeight, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
  have hlead :
      (dyadicWeight : ℂ) * lead rho (t+dyadicShift) =
        Complex.exp ((rho-1)*(dyadicShift : ℂ)) * lead rho t := by
    simp only [ha, lead, ← Complex.exp_add]
    congr 1
    unfold lambda
    push_cast
    ring
  have hweight : (dyadicWeight : ℂ) * Complex.exp (-(dyadicShift : ℂ)/2) = 1/2 := by
    rw [ha, ← Complex.exp_add,
      show -(dyadicShift : ℂ)/2 + -(dyadicShift : ℂ)/2 = -(dyadicShift : ℂ) by ring,
      ← Complex.ofReal_neg, ← Complex.ofReal_exp, exp_neg_dyadicShift] <;>
      simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have hdecay :
      (dyadicWeight : ℂ) * Complex.exp (-((t+dyadicShift : ℝ) : ℂ)/2) =
        (1/2 : ℂ) * Complex.exp (-(t : ℂ)/2) := by
    rw [show -((t+dyadicShift : ℝ) : ℂ)/2 = -(dyadicShift : ℂ)/2 + -(t : ℂ)/2 by
      push_cast
      ring, Complex.exp_add, ← mul_assoc, hweight]
  rw [(signed_response_integrable_and_eq hh hl hz ht).2.2]
  have hformula (u : ℝ) : explicitOutput rho u =
      (lead rho u - (1+rho*(u : ℂ))*Complex.exp (-(u : ℂ)/2)) / rho^2 := rfl
  simp only [hformula, signedRemainder, signedAmplitude, shiftedDecay]
  have hld := hlead
  have hdd := hdecay
  push_cast at hld hdd ⊢
  -- Isolate the two weighted shifted exponentials before clearing denominators.
  calc
    _ = (lead rho t - (1+rho*(t : ℂ))*Complex.exp (-(t : ℂ)/2)) / rho^2 -
        (((dyadicWeight : ℂ)*lead rho (t+dyadicShift)) -
          (1+rho*((t : ℂ)+(dyadicShift : ℂ))) *
            ((dyadicWeight : ℂ)*Complex.exp (-((t : ℂ)+(dyadicShift : ℂ))/2))) / rho^2 +
        (dyadicWeight : ℂ) * causal (q rho) initialProfile (t+dyadicShift) := by ring
    _ = _ := by
      rw [hld, hdd]
      field_simp [rho_ne_zero hh] <;> ring

private lemma signedAmplitude_ne_zero {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) : signedAmplitude rho ≠ 0 := by
  have hnorm : ‖Complex.exp ((rho-1)*(dyadicShift : ℂ))‖ < 1 := by
    rw [Complex.norm_exp, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.sub_re, Complex.one_re]
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (sub_neg.mpr hl) dyadicShift_pos)
  unfold signedAmplitude
  refine div_ne_zero (sub_ne_zero.mpr ?_) (pow_ne_zero 2 (rho_ne_zero hh))
  intro he
  rw [← he, norm_one] at hnorm
  exact (lt_irrefl (1 : ℝ)) hnorm

private def signedB0 (rho : ℂ) : ℝ :=
  4 - dyadicShift + (1+‖rho‖*dyadicShift)/(2*‖rho‖^2)

private def signedB1 (rho : ℂ) : ℝ :=
  1+1/(2*‖rho‖)

private def signedLoss (rho : ℂ) : ℝ :=
  2*‖signedAmplitude rho‖*(signedB0 rho/(1-rho.re) + signedB1 rho/(1-rho.re)^2)

private lemma signedB0_nonneg (rho : ℂ) : 0 ≤ signedB0 rho := by
  have hT : dyadicShift ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  unfold signedB0
  exact add_nonneg (by linarith) (div_nonneg
    (add_nonneg zero_le_one (mul_nonneg (norm_nonneg _) dyadicShift_pos.le))
    (by positivity))

private lemma signedB1_nonneg (rho : ℂ) : 0 ≤ signedB1 rho := by
  unfold signedB1
  positivity

private lemma shiftedDecay_bound (rho : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖shiftedDecay rho t‖ ≤
      ((1+‖rho‖*(dyadicShift+t))/(2*‖rho‖^2))*Real.exp (-t/2) := by
  have ha : |dyadicShift-t| ≤ dyadicShift+t := by
    rw [abs_le]
    constructor <;> linarith [dyadicShift_pos.le]
  have hb : ‖rho*((dyadicShift : ℂ)-(t : ℂ))-1‖ ≤ 1+‖rho‖*(dyadicShift+t) := by
    calc
      _ ≤ ‖rho*((dyadicShift : ℂ)-(t : ℂ))‖+‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖rho‖*|dyadicShift-t| + 1 := by
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, norm_one]
      _ ≤ _ := by
        rw [add_comm (1 : ℝ)]
        exact add_le_add (mul_le_mul_of_nonneg_left ha (norm_nonneg rho)) le_rfl
  have hre : (-(t : ℂ)/2).re = -t/2 := by simp
  simp only [shiftedDecay, norm_div, norm_mul, norm_pow, Complex.norm_two, Complex.norm_exp, hre]
  calc
    _ ≤ Real.exp (-t/2) * (1+‖rho‖*(dyadicShift+t))/(2*‖rho‖^2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le)
        (by positivity)
    _ = _ := by ring

private lemma signedRemainder_bound {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) (hz : riemannZeta rho = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖signedRemainder rho t‖ ≤ (signedB0 rho+signedB1 rho*t)*Real.exp (-t/2) := by
  unfold signedRemainder
  refine (norm_add_le _ _).trans ((add_le_add (shiftedDecay_bound rho ht)
    (initial_response_bound hh hl hz ht)).trans_eq ?_)
  have hn : ‖rho‖ ≠ 0 := norm_ne_zero_iff.mpr (rho_ne_zero hh)
  unfold signedB0 signedB1
  field_simp [hn] <;> ring

private lemma signed_output_pointwise {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) (hz : riemannZeta rho = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖signedAmplitude rho‖^2 * Real.exp ((2*rho.re-1)*t) -
      (2*‖signedAmplitude rho‖) *
        ((signedB0 rho+signedB1 rho*t)*Real.exp (-(1-rho.re)*t))
      ≤ ‖signedResponse rho t‖^2 := by
  let x := ‖signedAmplitude rho * lead rho t‖
  let y := ‖signedResponse rho t‖
  have hxy : x-y ≤ ‖signedRemainder rho t‖ := by
    have h := norm_sub_norm_le (signedAmplitude rho * lead rho t) (signedResponse rho t)
    rwa [show signedAmplitude rho * lead rho t - signedResponse rho t =
        -signedRemainder rho t by rw [signed_response_split hh hl hz ht]; ring, norm_neg] at h
  have ht' : x-y ≤ (signedB0 rho+signedB1 rho*t)*Real.exp (-t/2) :=
    hxy.trans (signedRemainder_bound hh hl hz ht)
  have hm := mul_le_mul_of_nonneg_left ht'
    (show 0 ≤ 2*x from mul_nonneg (by norm_num) (norm_nonneg _))
  have hsq : x^2 - 2*x*((signedB0 rho+signedB1 rho*t)*Real.exp (-t/2)) ≤ y^2 := by
    nlinarith only [hm, sq_nonneg (x-y)]
  have hx : x^2 = ‖signedAmplitude rho‖^2 * Real.exp ((2*rho.re-1)*t) := by
    dsimp only [x]
    rw [norm_mul, mul_pow, lead_norm_sq]
  have hprod : 2*x*((signedB0 rho+signedB1 rho*t)*Real.exp (-t/2)) =
      (2*‖signedAmplitude rho‖) *
        ((signedB0 rho+signedB1 rho*t)*Real.exp (-(1-rho.re)*t)) := by
    have hn : ‖lead rho t‖ = Real.exp ((rho.re-1/2)*t) := by
      simp [lead, lambda, Complex.norm_exp]
    dsimp only [x]
    rw [norm_mul, hn,
      show 2*(‖signedAmplitude rho‖*Real.exp ((rho.re-1/2)*t)) *
          ((signedB0 rho+signedB1 rho*t)*Real.exp (-t/2)) =
          (2*‖signedAmplitude rho‖) * ((signedB0 rho+signedB1 rho*t) *
            (Real.exp ((rho.re-1/2)*t)*Real.exp (-t/2))) by ring,
      ← Real.exp_add,
      show (rho.re-1/2)*t + -t/2 = -(1-rho.re)*t by ring]
  rw [hx, hprod] at hsq
  exact hsq

/-- The full K term with fixed explicit loss on every nonnegative prefix. -/
private theorem signed_prefix_energy_lower_bound {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) (hz : riemannZeta rho = 0) {U : ℝ} (hU : 0 ≤ U) :
    ‖signedAmplitude rho‖^2 * K rho.re U - signedLoss rho ≤ 400 * signedEnergy U := by
  let env : ℝ → ℝ :=
    fun t => (signedB0 rho+signedB1 rho*t)*Real.exp (-(1-rho.re)*t)
  have iEnv : IntervalIntegrable env volume 0 U :=
    (by unfold env; fun_prop : Continuous env).intervalIntegrable _ _
  have iK : IntervalIntegrable (fun t : ℝ => Real.exp ((2*rho.re-1)*t)) volume 0 U :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp ((2*rho.re-1)*t))).intervalIntegrable _ _
  have hEnv := affine_exp_integral (sub_pos.mpr hl) (signedB0 rho) (signedB1 rho)
  have hEnvPrefix : (∫ t in (0 : ℝ)..U, env t) ≤
      signedB0 rho/(1-rho.re) + signedB1 rho/(1-rho.re)^2 := by
    rw [← hEnv.2, intervalIntegral.integral_of_le hU]
    apply setIntegral_mono_set hEnv.1
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (add_nonneg (signedB0_nonneg rho)
        (mul_nonneg (signedB1_nonneg rho) ht.le)) (Real.exp_pos _).le
    · exact ae_of_all _ (fun t ht => ht.1)
  have hYoung := signed_prefix_transfer hh hl hz hU
  have hOut :
      ‖signedAmplitude rho‖^2 * K rho.re U -
        (2*‖signedAmplitude rho‖)*(∫ t in (0 : ℝ)..U, env t) ≤
        ∫ t in (0 : ℝ)..U, ‖signedResponse rho t‖^2 := by
    calc
      _ = ∫ t in (0 : ℝ)..U,
          ‖signedAmplitude rho‖^2 * Real.exp ((2*rho.re-1)*t) -
            (2*‖signedAmplitude rho‖)*env t := by
        rw [intervalIntegral.integral_sub (iK.const_mul _) (iEnv.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, K]
      _ ≤ _ := intervalIntegral.integral_mono_on hU
        ((iK.const_mul _).sub (iEnv.const_mul _)) hYoung.1
        (fun _ ht => signed_output_pointwise hh hl hz ht.1)
  have hLoss := mul_le_mul_of_nonneg_left hEnvPrefix
    (show 0 ≤ 2*‖signedAmplitude rho‖ from mul_nonneg (by norm_num) (norm_nonneg _))
  have hLower : ‖signedAmplitude rho‖^2 * K rho.re U - signedLoss rho ≤
      ∫ t in (0 : ℝ)..U, ‖signedResponse rho t‖^2 := by
    unfold signedLoss
    linarith only [hOut, hLoss]
  exact hLower.trans hYoung.2.2

private lemma signed_K_ge_time {beta U : ℝ} (hb : (1/2 : ℝ) ≤ beta)
    (hU : 0 ≤ U) : U ≤ K beta U := by
  have ie : IntervalIntegrable (fun t : ℝ => Real.exp ((2*beta-1)*t)) volume 0 U :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp ((2*beta-1)*t))).intervalIntegrable _ _
  have hm : (∫ _t in (0 : ℝ)..U, (1 : ℝ)) ≤
      ∫ t in (0 : ℝ)..U, Real.exp ((2*beta-1)*t) := by
    apply intervalIntegral.integral_mono_on hU intervalIntegrable_const ie
    intro t ht
    have hp : 0 ≤ (2*beta-1)*t := mul_nonneg (by linarith) ht.1
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hp
  simpa only [K, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using hm

/-- An explicit positive rate times the full K term on every sufficiently long prefix. -/
private theorem signed_eventual_prefix_lower_bound {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) (hz : riemannZeta rho = 0) :
    0 < ‖signedAmplitude rho‖^2 / 800 ∧
    ∀ U : ℝ, max 0 (2*signedLoss rho / ‖signedAmplitude rho‖^2) ≤ U →
      (‖signedAmplitude rho‖^2 / 800)*K rho.re U ≤ signedEnergy U := by
  have hn := norm_pos_iff.mpr (signedAmplitude_ne_zero hh hl)
  have hn2 : 0 < ‖signedAmplitude rho‖^2 := sq_pos_of_pos hn
  refine ⟨div_pos hn2 (by norm_num), ?_⟩
  intro U hU
  have h0 : 0 ≤ U := (le_max_left _ _).trans hU
  have hK := signed_K_ge_time hh h0
  have hthreshold : 2*signedLoss rho / ‖signedAmplitude rho‖^2 ≤ K rho.re U :=
    (le_max_right _ _).trans (hU.trans hK)
  have hLoss : 2*signedLoss rho ≤ ‖signedAmplitude rho‖^2 * K rho.re U :=
    by simpa only [mul_comm] using (div_le_iff₀ hn2).mp hthreshold
  have hbound := signed_prefix_energy_lower_bound hh hl hz h0
  have hhalf : (‖signedAmplitude rho‖^2 * K rho.re U)/2 ≤ 400 * signedEnergy U := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    linarith only [hbound, hLoss]
  calc
    _ = ((‖signedAmplitude rho‖^2 * K rho.re U)/2)/400 := by ring
    _ ≤ _ := (div_le_iff₀ (by norm_num : (0 : ℝ) < 400)).mpr
      (by simpa only [mul_comm] using hhalf)

private lemma dyadicSquare_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun x => mobiusDyadicDifference x ^ 2) volume a b := by
  have hm : Measurable mobiusPartialSum := by
    let F : ℕ → ℝ := fun n => ∑ k ∈ Finset.Icc 1 n,
      (ArithmeticFunction.moebius k : ℝ) / (k : ℝ)
    exact (measurable_of_countable F).comp Nat.measurable_floor
  have hd : Measurable mobiusDyadicDifference :=
    hm.sub (hm.comp (measurable_const.mul measurable_id))
  have hb (x : ℝ) : |mobiusPartialSum x| ≤ 1 := by
    have he : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    simpa only [mobiusPartialSum, reciprocalSum, he] using abs_reciprocalSum_le_one x
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (by simp [uIoc])
    (hd.pow_const 2).aestronglyMeasurable (M := 4) ?_
  filter_upwards with x
  have hdiff : |mobiusDyadicDifference x| ≤ 2 := by
    unfold mobiusDyadicDifference
    rw [abs_le]
    obtain ⟨hx₀, hx₁⟩ := abs_le.mp (hb x)
    obtain ⟨h2x₀, h2x₁⟩ := abs_le.mp (hb (2*x))
    constructor <;> linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  calc
    _ ≤ (2 : ℝ)^2 := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
    _ = 4 := by norm_num

private lemma signedProfile_eq (t : ℝ) :
    signedProfile t = Real.exp (t / 2) * mobiusDyadicDifference (Real.exp t) := by
  have he : Real.exp dyadicShift = 2 := Real.exp_log (by norm_num)
  have harg : Real.exp (t + dyadicShift) = 2 * Real.exp t := by
    rw [Real.exp_add, he, mul_comm]
  have hweight : dyadicWeight * Real.exp ((t + dyadicShift) / 2) = Real.exp (t / 2) := by
    rw [dyadicWeight, ← Real.exp_add]
    congr 1
    ring
  unfold signedProfile MobiusCausalKernel.h mobiusDyadicDifference
  rw [harg, ← mul_assoc, hweight, mul_sub]

/-- Exponential substitution for the signed floor-step profile. -/
private theorem signedEnergy_exp_transport {U : ℝ} (hU : 0 ≤ U) :
    IntervalIntegrable (fun t => signedProfile t ^ 2) volume 0 U ∧
    signedEnergy U = ∫ x in (1 : ℝ)..(Real.exp U), mobiusDyadicDifference x ^ 2 := by
  let f : ℝ → ℝ := fun x => mobiusDyadicDifference x ^ 2
  have hsq (t : ℝ) : signedProfile t ^ 2 = f (Real.exp t) * Real.exp t := by
    have he : Real.exp (t / 2) ^ 2 = Real.exp t := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [signedProfile_eq, mul_pow, he, mul_comm]
  have hi : IntervalIntegrable (fun t => f (Real.exp t) * Real.exp t) volume 0 U :=
    (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (a := (0 : ℝ)) (b := U) (f := Real.exp) (f' := Real.exp) (g := f)
      Real.continuous_exp.continuousOn (fun t _ => Real.hasDerivAt_exp t)
      (fun t _ => (Real.exp_pos t).le)).mpr (dyadicSquare_intervalIntegrable _ _)
  have hs := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := U) (f := Real.exp) (f' := Real.exp) (g := f)
    Real.continuous_exp.continuousOn (fun t _ => Real.hasDerivAt_exp t)
    (fun t _ => (Real.exp_pos t).le)
  refine ⟨hi.congr_uIoo (fun t _ => (hsq t).symm), ?_⟩
  calc
    signedEnergy U = ∫ t in (0 : ℝ)..U, f (Real.exp t) * Real.exp t := by
      apply intervalIntegral.integral_congr_Ioo_of_le hU
      intro t _
      exact hsq t
    _ = _ := by simpa only [Real.exp_zero, Function.comp_apply, f] using hs

/-- The literal dyadic-shell sum equals the signed prefix energy for every cutoff. -/
private theorem signedEnergy_eq_sum_mobiusDyadicShellEnergy (N : ℕ) :
    signedEnergy ((N : ℝ) * dyadicShift) =
      ∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k := by
  have hshift : 0 < dyadicShift := Real.log_pos (by norm_num)
  have hU : 0 ≤ (N : ℝ) * dyadicShift := mul_nonneg (Nat.cast_nonneg _) hshift.le
  have he : Real.exp ((N : ℝ) * dyadicShift) = (2 : ℝ) ^ N := by
    rw [dyadicShift, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (2 : ℝ) ^ k)
    (f := fun x => mobiusDyadicDifference x ^ 2) (μ := volume) (n := N)
    (fun k _ => dyadicSquare_intervalIntegrable _ _)
  rw [(signedEnergy_exp_transport hU).2, he]
  calc
    _ = ∑ k ∈ Finset.range N,
        ∫ x in ((2 : ℝ)^k)..((2 : ℝ)^(k+1)), mobiusDyadicDifference x ^ 2 := by
      simpa only [pow_zero] using hs.symm
    _ = _ := Finset.sum_congr rfl (fun k _ =>
      intervalIntegral.integral_of_le (pow_right_mono₀ (by norm_num) (Nat.le_succ k)))

/-- Each zero in the closed right half of the open critical strip forces the full
exponential energy scale on all sufficiently long prefixes of the signed shells. -/
theorem signed_dyadic_eventual_prefix_lower_bound {rho : ℂ} (hh : (1 / 2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) (hz : riemannZeta rho = 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * K rho.re ((N : ℝ) * Real.log 2) ≤
        ∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k := by
  obtain ⟨hc, hbound⟩ := signed_eventual_prefix_lower_bound hh hl hz
  let U₀ := max 0 (2 * signedLoss rho / ‖signedAmplitude rho‖ ^ 2)
  refine ⟨‖signedAmplitude rho‖ ^ 2 / 800, hc, Nat.ceil (U₀ / dyadicShift), ?_⟩
  intro N hN
  have hcut : U₀ / dyadicShift ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  rw [← signedEnergy_eq_sum_mobiusDyadicShellEnergy]
  exact hbound _ ((div_le_iff₀ dyadicShift_pos).mp hcut)

#print axioms signed_dyadic_eventual_prefix_lower_bound

end D5.S3.Weil.Mertens.MobiusDyadicEnergy

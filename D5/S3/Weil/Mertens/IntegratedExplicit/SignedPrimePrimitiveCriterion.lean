/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveCriterion
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Growth of the signed prime tail primitive bounds zeta zeros, and its slope from 5040 equals minus two exactly under RH. -/

import D5.S3.Analytic.Laplace.EulerPoleObstruction
import D5.S3.Analytic.Laplace.PositiveLaplaceContinuation
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtRealRegular
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
import D5.S3.Weil.Probability.AnalyticLogarithmicContinuation
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
import Mathlib.Analysis.Complex.Convex
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
The signed primitive of the actual prime-only Chebyshev tail controls the right
edge of the zero strip. In logarithmic coordinates, prime powers change the
primitive by at most a linear term. Integration by parts puts the original
Mangoldt transform in terms of the complete primitive, which has a Laplace
transform on the full open half-plane to the right of the growth exponent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Asymptotics Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U)
open D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity (complete_chebyshev_tail_identity)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
  (primeTail prime_integrable prime_power_window_correction)
open D5.S3.Weil.Probability.AnalyticLogarithmicContinuation
  (local_logarithmic_equation_zero_free)
open D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
  (golden_right_half_strip_implies_rh)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveCriterion

open D5.S3.Analytic.Laplace

private def cutoff : ℝ := Real.log 2

private lemma cutoff_nonneg : 0 ≤ cutoff := Real.log_nonneg (by norm_num)

private lemma two_le_exp_of_cutoff_le {t : ℝ} (ht : cutoff ≤ t) : 2 ≤ Real.exp t := by
  simpa only [cutoff, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
    Real.exp_le_exp.mpr ht

/-- The signed primitive of the tail of the actual Chebyshev theta count. -/
def signedPrimePrimitive (T : ℝ) : ℝ :=
  ∫ x in 2..Real.exp T, primeTail x / Real.sqrt x

/-- Eventual exponential bounds with arbitrarily small positive slack. -/
def HasExponentBound (β : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ t in atTop, ‖f t‖ ≤ C * Real.exp ((β + ε - 1 / 2) * t)

private def completeDensity (t : ℝ) : ℝ :=
  Real.exp (-t / 2) * U (Real.exp t)

private def completePrimitive (T : ℝ) : ℝ :=
  ∫ t in cutoff..T, completeDensity t

private lemma completeDensity_continuous : Continuous completeDensity :=
  (show Continuous (fun t : ℝ => Real.exp (-t / 2)) by fun_prop).mul U_exp_continuous

private lemma completePrimitive_hasDerivAt (t : ℝ) :
    HasDerivAt completePrimitive (completeDensity t) t :=
  intervalIntegral.integral_hasDerivAt_right (completeDensity_continuous.intervalIntegrable _ _)
    completeDensity_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    completeDensity_continuous.continuousAt

private lemma completePrimitive_continuous : Continuous completePrimitive :=
  continuous_iff_continuousAt.mpr fun t => (completePrimitive_hasDerivAt t).continuousAt

private def primeLogDensity (t : ℝ) : ℝ :=
  primeTail (Real.exp t) / Real.sqrt (Real.exp t) * Real.exp t

private lemma primeDensity_continuousOn :
    ContinuousOn (fun x : ℝ => primeTail x / Real.sqrt x) (Ici 1) :=
  prime_integrable.continuousOn_Ici_primitive_Ioi.div Real.continuous_sqrt.continuousOn
    (fun _ hx => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (mem_Ici.mp hx))).ne')

/-- Anchoring the signed window at 5040 changes the late primitive by a fixed integral. -/
private theorem signedPrimePrimitive_eq_from_5040 {T : ℝ} (hT : Real.log 5040 ≤ T) :
    signedPrimePrimitive T =
      (∫ x in 2..(5040 : ℝ), primeTail x / Real.sqrt x) +
        (∫ x in (5040 : ℝ)..Real.exp T, primeTail x / Real.sqrt x) := by
  have hle : (5040 : ℝ) ≤ Real.exp T := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 5040)] using Real.exp_le_exp.mpr hT
  have hi {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable (fun x : ℝ => primeTail x / Real.sqrt x) volume a b :=
    (primeDensity_continuousOn.mono
      (fun _ hx => ha.trans ((uIcc_of_le hab ▸ hx).1))).intervalIntegrable
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hi (by norm_num) (by norm_num : (2 : ℝ) ≤ 5040))
    (hi (by norm_num) hle)).symm

private lemma primeLogDensity_continuousOn : ContinuousOn primeLogDensity (Ici cutoff) := by
  have hm : MapsTo Real.exp (Ici cutoff) (Ici (1 : ℝ)) := fun _ hx =>
    (by norm_num : (1 : ℝ) ≤ 2).trans (two_le_exp_of_cutoff_le hx)
  exact (primeDensity_continuousOn.comp Real.continuous_exp.continuousOn hm).mul
    Real.continuous_exp.continuousOn

private lemma signedPrimePrimitive_log {T : ℝ} (hT : cutoff ≤ T) :
    signedPrimePrimitive T = ∫ t in cutoff..T, primeLogDensity t := by
  have hc := intervalIntegral.integral_comp_mul_deriv'
    (a := cutoff) (b := T) (f := Real.exp) (f' := Real.exp)
    (g := fun x => primeTail x / Real.sqrt x)
    (fun t _ => Real.hasDerivAt_exp t) Real.continuous_exp.continuousOn
    (primeDensity_continuousOn.mono (by
      rintro _ ⟨t, ht, rfl⟩
      exact (by norm_num : (1 : ℝ) ≤ 2).trans
        (two_le_exp_of_cutoff_le ((uIcc_of_le hT ▸ ht).1))))
  simpa only [cutoff, Real.exp_log (by norm_num : (0 : ℝ) < 2), Function.comp_apply,
    signedPrimePrimitive, primeLogDensity] using hc.symm

private lemma completeDensity_eq {t : ℝ} (ht : cutoff ≤ t) :
    completeDensity t = -(Q (Real.exp t) / Real.sqrt (Real.exp t) * Real.exp t) := by
  have hQ := complete_chebyshev_tail_identity chebyshev_error_kernel_integrable
    (two_le_exp_of_cutoff_le ht)
  change Q (Real.exp t) = _ at hQ
  have hU : U (Real.exp t) = -Q (Real.exp t) * Real.exp t := by
    rw [hQ, U]
    field_simp [(Real.exp_pos t).ne']
    ring
  rw [completeDensity, hU, show -t / 2 = -(t / 2) by ring, Real.exp_neg, Real.exp_half]
  ring

/-- The signed correction stays linear in log coordinates, with the same
theta and psi tails used in the arithmetic transform. -/
private lemma primitive_prime_power_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T, cutoff ≤ T →
      ‖completePrimitive T + signedPrimePrimitive T‖ ≤ C * T := by
  obtain ⟨D, hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let C := max D 0
  have hC : 0 ≤ C := le_max_right _ _
  have hcorr := (prime_power_window_correction.2 C
    (fun x _ => (hD x).trans (mul_le_mul_of_nonneg_right (le_max_left D 0)
      (Real.sqrt_nonneg x)))).1
  refine ⟨2 * C, by positivity, fun T hT => ?_⟩
  have hp : IntervalIntegrable primeLogDensity volume cutoff T :=
    (primeLogDensity_continuousOn.mono (fun _ ht => (uIcc_of_le hT ▸ ht).1)).intervalIntegrable
  have hf : IntervalIntegrable completeDensity volume cutoff T :=
    completeDensity_continuous.intervalIntegrable _ _
  have hg := hf.add hp
  have hpoint (t : ℝ) (ht : cutoff ≤ t) :
      ‖completeDensity t + primeLogDensity t‖ ≤ 2 * C := by
    have hs := Real.sqrt_pos.mpr (Real.exp_pos t)
    have hsquare : Real.exp t / Real.sqrt (Real.exp t) = Real.sqrt (Real.exp t) := by
      apply (div_eq_iff hs.ne').2
      rw [← pow_two, Real.sq_sqrt (Real.exp_nonneg t)]
    have hd := hcorr (Real.exp t) ((by norm_num : (1 : ℝ) ≤ 2).trans
      (two_le_exp_of_cutoff_le ht))
    have heq : completeDensity t + primeLogDensity t =
        -((Q (Real.exp t) - primeTail (Real.exp t)) * Real.sqrt (Real.exp t)) := by
      simp only [completeDensity_eq ht, primeLogDensity, div_mul_eq_mul_div, mul_div_assoc,
        hsquare]
      ring
    rw [heq, Real.norm_eq_abs, abs_neg, abs_of_nonneg (mul_nonneg hd.1 hs.le)]
    calc
      _ ≤ (2 * C / Real.sqrt (Real.exp t)) * Real.sqrt (Real.exp t) :=
        mul_le_mul_of_nonneg_right hd.2 hs.le
      _ = _ := div_mul_cancel₀ _ hs.ne'
  rw [signedPrimePrimitive_log hT, completePrimitive, ← intervalIntegral.integral_add hf hp]
  calc
    _ ≤ ∫ t in cutoff..T, ‖completeDensity t + primeLogDensity t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hT
    _ ≤ ∫ _ in cutoff..T, 2 * C :=
      intervalIntegral.integral_mono_on hT hg.norm
        (continuous_const.intervalIntegrable _ _) (fun t ht => hpoint t ht.1)
    _ = (T - cutoff) * (2 * C) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ 2 * C * T := by
      rw [mul_comm (2 * C) T]
      exact mul_le_mul_of_nonneg_right (sub_le_self _ cutoff_nonneg) (by positivity)

private lemma eventually_pow_le_exp (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, t ^ m ≤ Real.exp (ε * t) := by
  have h := (Asymptotics.isLittleO_iff.mp (isLittleO_pow_exp_pos_mul_atTop m hε))
    one_pos
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht0 m),
    abs_of_pos (Real.exp_pos _)] using ht

private lemma completePrimitive_growth {β : ℝ} (hβ : 1 / 2 ≤ β)
    (h : HasExponentBound β signedPrimePrimitive) : HasExponentBound β completePrimitive := by
  obtain ⟨D, hD, hgap⟩ := primitive_prime_power_bound
  intro ε hε
  obtain ⟨C, hC, hP⟩ := h ε hε
  refine ⟨D + C, add_nonneg hD hC, ?_⟩
  filter_upwards [hP, eventually_ge_atTop cutoff, eventually_pow_le_exp 1 hε] with t ht htlog htlin
  rw [pow_one] at htlin
  have hrate : Real.exp (ε * t) ≤ Real.exp ((β + ε - 1 / 2) * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (cutoff_nonneg.trans htlog))
  calc
    ‖completePrimitive t‖ = ‖(completePrimitive t + signedPrimePrimitive t) -
        signedPrimePrimitive t‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖completePrimitive t + signedPrimePrimitive t‖ + ‖signedPrimePrimitive t‖ :=
      norm_sub_le _ _
    _ ≤ D * Real.exp ((β + ε - 1 / 2) * t) + C * Real.exp ((β + ε - 1 / 2) * t) :=
      add_le_add ((hgap t htlog).trans (mul_le_mul_of_nonneg_left (htlin.trans hrate) hD)) ht
    _ = _ := by ring

private lemma exponentBound_of_polynomial {β : ℝ} {f : ℝ → ℝ} {m : ℕ}
    (h : f =O[atTop] (fun t : ℝ => Real.exp ((β - 1 / 2) * t) * (1 + t) ^ m)) :
    HasExponentBound β f := by
  obtain ⟨C, hC, hb⟩ := Asymptotics.isBigO_iff'.mp h
  intro ε hε
  refine ⟨C * 2 ^ m, by positivity, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ), eventually_pow_le_exp m hε] with t ht ht1 hp
  have hnon : 0 ≤ (1 + t) ^ m := pow_nonneg (by linarith) _
  have ht' : ‖f t‖ ≤ C * (Real.exp ((β - 1 / 2) * t) * (1 + t) ^ m) := by
    simpa only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg hnon]
      using ht
  have hpow : (1 + t) ^ m ≤ 2 ^ m * Real.exp (ε * t) := calc
    _ ≤ (2 * t) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) _
    _ ≤ _ := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hp (by positivity)
  calc
    _ ≤ C * (Real.exp ((β - 1 / 2) * t) * (1 + t) ^ m) := ht'
    _ ≤ C * (Real.exp ((β - 1 / 2) * t) * (2 ^ m * Real.exp (ε * t))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le) hC.le
    _ = (C * 2 ^ m) * (Real.exp ((β - 1 / 2) * t) * Real.exp (ε * t)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

private lemma kernel_continuous {g : ℝ → ℝ} (hg : Continuous g) (s : ℂ) :
    Continuous (EulerPoleObstruction.kernel g s) :=
  (show Continuous (fun t : ℝ => Complex.exp (-s * (t : ℂ))) by fun_prop).mul
    (Complex.continuous_ofReal.comp hg)

private lemma kernel_norm (g : ℝ → ℝ) (s : ℂ) (t : ℝ) :
    ‖EulerPoleObstruction.kernel g s t‖ = Real.exp (-s.re * t) * ‖g t‖ := by
  simp [EulerPoleObstruction.kernel, Complex.norm_exp, Complex.mul_re]

/-- Absolute convergence and the boundary limit for the damped primitive. -/
private lemma damped_primitive {β : ℝ} (h : HasExponentBound β completePrimitive)
    {s : ℂ} (hs : β < s.re) :
    IntegrableOn (EulerPoleObstruction.kernel completePrimitive (s - 1 / 2)) (Ioi cutoff) ∧
      Tendsto (EulerPoleObstruction.kernel completePrimitive (s - 1 / 2)) atTop (𝓝 0) := by
  let ε := (s.re - β) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, _, hC⟩ := h ε hε
  let K := EulerPoleObstruction.kernel completePrimitive (s - 1 / 2)
  have hK : Continuous K := kernel_continuous completePrimitive_continuous _
  have hmajor : ∀ᶠ t : ℝ in atTop, ‖K t‖ ≤ C * Real.exp (-ε * t) := by
    filter_upwards [hC] with t ht
    dsimp only [K]
    rw [kernel_norm]
    calc
      _ ≤ Real.exp (-(s - 1 / 2).re * t) *
          (C * Real.exp ((β + ε - 1 / 2) * t)) :=
        mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
      _ = C * (Real.exp (-(s - 1 / 2).re * t) * Real.exp ((β + ε - 1 / 2) * t)) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        have hre : (s - 1 / 2).re = s.re - 1 / 2 := by
          have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
            simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
          simp only [hhalf, Complex.sub_re, Complex.ofReal_re]
        rw [hre]
        congr 2
        dsimp only [ε]
        ring
  obtain ⟨R, hR⟩ := eventually_atTop.mp hmajor
  let V := max cutoff R
  have hV : cutoff ≤ V := le_max_left _ _
  have htail : IntegrableOn K (Ioi V) := by
    refine ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) V).const_mul C).mono'
      hK.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hR t ((le_max_right _ _).trans ht.le)
  have hhead : IntegrableOn K (Ioc cutoff V) :=
    hK.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  constructor
  · rw [← Ioc_union_Ioi_eq_Ioi hV]
    exact hhead.union htail
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hdecay : Tendsto (fun t : ℝ => Real.exp (-ε * t)) atTop (𝓝 0) := by
      have hscale : Tendsto (fun t : ℝ => ε * t) atTop atTop :=
        (tendsto_const_mul_atTop_of_pos hε).mpr tendsto_id
      simpa only [Function.comp_def, neg_mul] using
        Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
    exact squeeze_zero' (Eventually.of_forall fun t => norm_nonneg (K t)) hmajor
      (by simpa only [mul_zero] using hdecay.const_mul C)

private def primitiveLaplace (s : ℂ) : ℂ :=
  ∫ t in Ioi cutoff, EulerPoleObstruction.kernel completePrimitive (s - 1 / 2) t

private lemma primitiveLaplace_analytic {β : ℝ} (h : HasExponentBound β completePrimitive) :
    AnalyticOnNhd ℂ primitiveLaplace {s : ℂ | β < s.re} := by
  intro s hs
  change β < s.re at hs
  let σ := (β + s.re) / 2
  have hσ : β < σ := by dsimp [σ]; linarith
  have hσs : σ < s.re := by dsimp [σ]; linarith
  let g (t : ℝ) := Real.exp (-(σ - 1 / 2) * t) * completePrimitive t
  have hg : IntegrableOn g (Ioi cutoff) := by
    have he : EulerPoleObstruction.kernel completePrimitive ((σ : ℂ) - 1 / 2) =
        (fun t : ℝ => (g t : ℂ)) := by
      funext t
      simp only [EulerPoleObstruction.kernel, g, Complex.ofReal_mul, Complex.ofReal_exp,
        Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_ofNat]
    have hi := (damped_primitive h (s := (σ : ℂ)) (by simpa using hσ)).1
    rw [he] at hi
    exact IntegrableOn.iff_ofReal.mpr hi
  have heq : primitiveLaplace =
      (fun z : ℂ => ∫ t in Ioi cutoff, EulerPoleObstruction.kernel g z t) ∘
        (fun z : ℂ => z - (σ : ℂ)) := by
    funext z
    change (∫ t in Ioi cutoff, EulerPoleObstruction.kernel completePrimitive (z - 1 / 2) t) =
      ∫ t in Ioi cutoff, EulerPoleObstruction.kernel g (z - (σ : ℂ)) t
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [EulerPoleObstruction.kernel, g, Complex.ofReal_mul, Complex.ofReal_exp,
      Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [heq]
  have ha := EulerPoleObstruction.tail_analytic hg cutoff_nonneg (s - (σ : ℂ))
    (by simpa only [mem_ofPred_eq, Complex.sub_re, Complex.ofReal_re] using sub_pos.mpr hσs)
  exact ha.comp (f := fun z : ℂ => z - (σ : ℂ)) (x := s)
    (analyticAt_id.sub analyticAt_const)

private def completeHead (s : ℂ) : ℂ :=
  EulerPoleObstruction.finiteHead (fun t => U (Real.exp t)) 0 cutoff s

private def continuedTransform (s : ℂ) : ℂ :=
  completeHead s + (s - 1 / 2) * primitiveLaplace s

private lemma continuedTransform_analytic {β : ℝ} (h : HasExponentBound β completePrimitive) :
    AnalyticOnNhd ℂ continuedTransform {s : ℂ | β < s.re} := by
  have hhead : Differentiable ℂ completeHead :=
    EulerPoleObstruction.finiteHead_entire
      (U_exp_continuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  intro s hs
  exact (hhead.analyticAt s).add
    ((analyticAt_id.sub analyticAt_const).mul (primitiveLaplace_analytic h s hs))

private lemma weighted_density (s : ℂ) (t : ℝ) :
    EulerPoleObstruction.kernel completeDensity (s - 1 / 2) t =
      EulerPoleObstruction.kernel (fun y => U (Real.exp y)) s t := by
  simp only [EulerPoleObstruction.kernel, completeDensity, Complex.ofReal_mul,
    Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat,
    ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Integration by parts from log 2 to infinity, where both boundary terms vanish. -/
private lemma tail_integration_by_parts {β : ℝ} (h : HasExponentBound β completePrimitive)
    {s : ℂ} (hs : β < s.re)
    (hu : IntegrableOn (EulerPoleObstruction.kernel (fun t => U (Real.exp t)) s) (Ioi cutoff)) :
    (∫ t in Ioi cutoff, EulerPoleObstruction.kernel (fun y => U (Real.exp y)) s t) =
      (s - 1 / 2) * primitiveLaplace s := by
  let a : ℂ := s - 1 / 2
  let K := EulerPoleObstruction.kernel completePrimitive a
  let V := EulerPoleObstruction.kernel (fun t => U (Real.exp t)) s
  obtain ⟨hK, hlim⟩ := damped_primitive h hs
  have hd (t : ℝ) : HasDerivAt K (V t - a * K t) t := by
    have he := ((hasDerivAt_id t).ofReal_comp.const_mul (-a)).cexp
    have hp := he.mul (completePrimitive_hasDerivAt t).ofReal_comp
    convert hp using 1
    · rfl
    · change EulerPoleObstruction.kernel (fun y => U (Real.exp y)) s t - a * K t = _
      rw [← weighted_density]
      dsimp only [K, EulerPoleObstruction.kernel, a, id_eq, Complex.ofReal_one]
      ring
  have hb : K cutoff = 0 := by simp [K, EulerPoleObstruction.kernel, completePrimitive]
  have hi : IntegrableOn (fun t => V t - a * K t) (Ioi cutoff) := hu.sub (hK.const_mul a)
  have hparts := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hd t) hi hlim
  rw [hb, sub_zero, integral_sub hu (hK.const_mul a), integral_const_mul] at hparts
  exact sub_eq_zero.mp hparts

private lemma continuedTransform_eq {β : ℝ} (hβ : β ≤ 1)
    (h : HasExponentBound β completePrimitive) {s : ℂ} (hs : 1 < s.re) :
    continuedTransform s = CompleteMangoldtLaurent.transform s := by
  have hsource := CompleteMangoldtLaurent.transform_integral_and_zero_germs.1 s hs
  let V := EulerPoleObstruction.kernel (fun t => U (Real.exp t)) s
  have hi : IntegrableOn V (Ioi 0) := hsource.1
  have ht := hi.mono_set (Ioi_subset_Ioi cutoff_nonneg)
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hi.mono_set Ioc_subset_Ioi_self) ht
  rw [Ioc_union_Ioi_eq_Ioi cutoff_nonneg] at hsplit
  change (∫ t in Ioi (0 : ℝ), V t) = completeHead s + (∫ t in Ioi cutoff, V t) at hsplit
  rw [tail_integration_by_parts h (hβ.trans_lt hs) ht] at hsplit
  exact hsplit.symm.trans hsource.2

private lemma zetaOne_eq {s : ℂ} (hs : s ≠ 1) :
    riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]

private lemma zetaOne_deriv {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta₁ s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have heq : riemannZeta₁ =ᶠ[𝓝 s] (fun z => (z - 1) * riemannZeta z) := by
    filter_upwards [compl_singleton_mem_nhds hs] with z hz
    exact zetaOne_eq (by simpa only [mem_compl_iff, mem_singleton_iff] using hz)
  rw [heq.deriv_eq]
  have hd := ((hasDerivAt_id s).sub_const (1 : ℂ)).mul
    ((_root_.analyticAt_riemannZeta hs).differentiableAt.hasDerivAt)
  change deriv ((fun z : ℂ => z - 1) * riemannZeta) s = _
  simpa only [id_eq, one_mul, add_comm] using hd.deriv

private def odeCoefficient (L : ℂ → ℂ) (s : ℂ) : ℂ :=
  ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) * s - 1 - s * (s - 1) * L s

private lemma zetaOne_is_solution {L : ℂ → ℂ} {s : ℂ} (hs : 1 < s.re)
    (hL : L s = CompleteMangoldtLaurent.transform s) :
    deriv riemannZeta₁ s = odeCoefficient L s * riemannZeta₁ s := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hζ := riemannZeta_ne_zero_of_one_lt_re hs
  rw [zetaOne_deriv hs1, zetaOne_eq hs1, odeCoefficient, hL, CompleteMangoldtLaurent.transform]
  field_simp [hs0, sub_ne_zero.mpr hs1, hζ]
  ring

/-- The growth exponent bounds the real part of every zero of the actual zeta function. -/
theorem zeta_zero_re_le_of_signedPrimePrimitive_exponent {β : ℝ}
    (hβ : 1 / 2 ≤ β) (hβ1 : β < 1) (h : HasExponentBound β signedPrimePrimitive)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) : ρ.re ≤ β := by
  have hF := completePrimitive_growth hβ h
  let L := continuedTransform
  let G := odeCoefficient L
  let H : Set ℂ := {s | β < s.re}
  have hH : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected H := (convex_halfSpace_re_gt β).isPreconnected
  have hζ : AnalyticOnNhd ℂ riemannZeta₁ H :=
    fun s _ => differentiable_riemannZeta₁.analyticAt s
  have hG : AnalyticOnNhd ℂ G H := by
    intro s hs
    have hlinear : AnalyticAt ℂ
        (fun z : ℂ => ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) * z - 1) s :=
      (analyticAt_const.mul analyticAt_id).sub analyticAt_const
    exact hlinear.sub
      ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul
        (continuedTransform_analytic hF s hs))
  have htwo : 1 < (2 : ℂ).re := by norm_num
  have htwo1 : (2 : ℂ) ≠ 1 := by norm_num
  have hbase : riemannZeta₁ 2 ≠ 0 := by
    rw [zetaOne_eq htwo1]
    exact mul_ne_zero (sub_ne_zero.mpr htwo1) (riemannZeta_ne_zero_of_one_lt_re htwo)
  have hlocal : deriv riemannZeta₁ =ᶠ[𝓝 (2 : ℂ)] (fun s => G s * riemannZeta₁ s) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds htwo]
      with s hs
    exact zetaOne_is_solution hs (continuedTransform_eq hβ1.le hF hs)
  have hfree := (local_logarithmic_equation_zero_free hH hconn hζ hG
    (show (2 : ℂ) ∈ H from hβ1.trans htwo) hbase hlocal).2
  by_contra! hr
  have hρ1 : ρ ≠ 1 := fun he => riemannZeta_one_ne_zero (he ▸ hρ)
  exact hfree ρ hr (by rw [zetaOne_eq hρ1, hρ, mul_zero])

/-- A fixed polynomial factor allows the same zero boundary, including at beta = 1/2. -/
private theorem zeta_zero_re_le_of_signedPrimePrimitive_polynomial {β : ℝ} {m : ℕ}
    (hβ : 1 / 2 ≤ β) (hβ1 : β < 1)
    (h : signedPrimePrimitive =O[atTop]
      (fun t : ℝ => Real.exp ((β - 1 / 2) * t) * (1 + t) ^ m))
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) : ρ.re ≤ β :=
  zeta_zero_re_le_of_signedPrimePrimitive_exponent hβ hβ1 (exponentBound_of_polynomial h) hρ

/-- Any fixed polynomial growth of the actual signed primitive implies RH. -/
private theorem riemannHypothesis_of_signedPrimePrimitive_polynomial {m : ℕ}
    (h : signedPrimePrimitive =O[atTop] (fun t : ℝ => (1 + t) ^ m)) :
    RiemannHypothesis := by
  refine golden_right_half_strip_implies_rh (fun ρ hρ hright _ => ?_)
  have hb : signedPrimePrimitive =O[atTop]
      (fun t : ℝ => Real.exp (((1 / 2 : ℝ) - 1 / 2) * t) * (1 + t) ^ m) := by simpa using h
  exact (not_lt_of_ge
    (zeta_zero_re_le_of_signedPrimePrimitive_polynomial le_rfl (by norm_num) hb hρ)) hright

section SignedPrimePrimitiveSlope

open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
  (actualData actualOccurrenceEquiv actualZero actual_height_gt_ten)
open D5.S3.Weil.ZetaBridge.RhLocatesZeroData (zeroData_zero_on_critical_line_of_rh)

private def normalizedActualZeroSeries (t : ℝ) : ℂ :=
  (Real.exp (-t / 2) : ℂ) * actualH t

private lemma normalizedActualZeroSeries_continuous : Continuous normalizedActualZeroSeries :=
  (Complex.continuous_ofReal.comp
    (show Continuous (fun t : ℝ => Real.exp (-t / 2)) by fun_prop)).mul actualH_continuous

private def actualZeroFrequency (k : ℕ) : ℂ :=
  actualZero k - ((1 / 2 : ℝ) : ℂ)

private lemma actualZeroMode_norm (hRH : RiemannHypothesis) (k : ℕ) (t : ℝ) :
    ‖Complex.exp (actualZeroFrequency k * (t : ℂ))‖ = 1 := by
  have hline : (actualZero k).re = 1 / 2 := by
    simpa only [actualZero, D5.S3.Weil.Convention.criticalAbscissa] using
      zeroData_zero_on_critical_line_of_rh hRH actualData (actualOccurrenceEquiv k).1
  have hfreq : (actualZeroFrequency k).re = 0 := by
    simp only [actualZeroFrequency, Complex.sub_re, Complex.ofReal_re, hline, sub_self]
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    hfreq, zero_mul, mul_zero, sub_zero, Real.exp_zero]

private lemma normalizedActualZeroSeries_hasSum (t : ℝ) :
    HasSum (fun k : ℕ => actualCoeff k * Complex.exp (actualZeroFrequency k * (t : ℂ)))
      (normalizedActualZeroSeries t) := by
  have hmode (k : ℕ) :
      actualCoeff k * Complex.exp (actualZeroFrequency k * (t : ℂ)) =
        (Real.exp (-t / 2) : ℂ) * (actualCoeff k * Complex.exp ((t : ℂ) * actualZero k)) := by
    have he : actualZeroFrequency k * (t : ℂ) =
        ((-t / 2 : ℝ) : ℂ) + (t : ℂ) * actualZero k := by
      simp only [actualZeroFrequency, Complex.ofReal_div, Complex.ofReal_neg,
        Complex.ofReal_one, Complex.ofReal_ofNat]
      ring
    rw [he, Complex.exp_add, ← Complex.ofReal_exp]
    ring
  simp_rw [hmode]
  exact (actualH_summable t).hasSum.mul_left (Real.exp (-t / 2) : ℂ)

-- Use the termwise integration argument of RHPrimeWindowMean with the public
-- occurrence-series API. The height bound controls both endpoint terms.
private lemma normalizedActualZeroSeries_window_bound
    (hRH : RiemannHypothesis) (a b : ℝ) :
    ‖∫ t in a..b, normalizedActualZeroSeries t‖ ≤ (∑' k : ℕ, ‖actualCoeff k‖) / 5 := by
  let term (k : ℕ) (t : ℝ) := actualCoeff k * Complex.exp (actualZeroFrequency k * (t : ℂ))
  have hs := actualCoeff_hasSum.summable.norm
  have hi : HasSum (fun k : ℕ => ∫ t in a..b, term k t)
      (∫ t in a..b, normalizedActualZeroSeries t) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k (_ : ℝ) => ‖actualCoeff k‖)
    · intro k
      exact (show Continuous (term k) by dsimp [term]; fun_prop).aestronglyMeasurable
    · intro k
      exact ae_of_all _ fun t _ => by
        simp only [term, norm_mul, actualZeroMode_norm hRH, mul_one, le_refl]
    · exact ae_of_all _ fun _ _ => hs
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun t _ => normalizedActualZeroSeries_hasSum t
  rw [← hi.tsum_eq, div_eq_mul_inv]
  apply tsum_of_norm_bounded (hs.hasSum.mul_right ((5 : ℝ)⁻¹))
  intro k
  have him : (actualZeroFrequency k).im = (actualZero k).im := by
    simp only [actualZeroFrequency, Complex.sub_im, Complex.ofReal_im, sub_zero]
  have hn : 10 < ‖actualZeroFrequency k‖ := by
    have hh := actual_height_gt_ten (actualZero k)
      (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)
    exact hh.trans_le (by simpa only [him] using Complex.abs_im_le_norm (actualZeroFrequency k))
  have hf : actualZeroFrequency k ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    norm_num at hn
  rw [show (∫ t in a..b, term k t) = actualCoeff k *
        ((Complex.exp (actualZeroFrequency k * (b : ℂ)) -
          Complex.exp (actualZeroFrequency k * (a : ℂ))) / actualZeroFrequency k) by
        change (∫ t in a..b, actualCoeff k * Complex.exp (actualZeroFrequency k * (t : ℂ))) = _
        rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hf],
    norm_mul, norm_div]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc
    _ ≤ (1 + 1) / ‖actualZeroFrequency k‖ := by
      refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
      simpa only [actualZeroMode_norm hRH] using
        norm_sub_le (Complex.exp (actualZeroFrequency k * (b : ℂ)))
          (Complex.exp (actualZeroFrequency k * (a : ℂ)))
    _ ≤ (1 + 1) / (10 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn.le
    _ = (5 : ℝ)⁻¹ := by norm_num

private lemma normalizedActualZeroSeries_re_average (hRH : RiemannHypothesis) :
    Tendsto (fun T : ℝ => (∫ t in cutoff..T, (normalizedActualZeroSeries t).re) / T)
      atTop (𝓝 0) := by
  let C := (∑' k : ℕ, ‖actualCoeff k‖) / 5
  have hC : Tendsto (fun T : ℝ => C / T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul C
  refine squeeze_zero_norm' ?_ hC
  filter_upwards [eventually_ge_atTop cutoff, eventually_gt_atTop (0 : ℝ)] with T hT hTpos
  have hre : (∫ t in cutoff..T, (normalizedActualZeroSeries t).re) =
      (∫ t in cutoff..T, normalizedActualZeroSeries t).re := by
    rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT]
    exact integral_re (normalizedActualZeroSeries_continuous.intervalIntegrable cutoff T).1
  rw [norm_div, Real.norm_of_nonneg hTpos.le, hre]
  exact div_le_div_of_nonneg_right
    ((Complex.abs_re_le_norm _).trans (normalizedActualZeroSeries_window_bound hRH cutoff T))
    hTpos.le

private lemma integral_average_tendsto_zero {a : ℝ} {f : ℝ → ℝ}
    (ha : 0 ≤ a) (hf : ContinuousOn f (Ici a)) (h : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => (∫ t in a..T, f t) / T) atTop (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero] at h ⊢
  intro ε hε
  obtain ⟨R, hR⟩ := eventually_atTop.mp (h (ε / 2) (by positivity))
  let b := max a R
  have hab : a ≤ b := le_max_left a R
  have hb : 0 ≤ b := ha.trans hab
  have hi {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) : IntervalIntegrable f volume u v :=
    (hf.mono (fun _ ht => hu.trans ((uIcc_of_le huv ▸ ht).1))).intervalIntegrable
  let C := ‖∫ t in a..b, f t‖
  have hC : Tendsto (fun T : ℝ => C / T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul C
  filter_upwards [eventually_ge_atTop b, eventually_gt_atTop (0 : ℝ),
    hC.eventually_lt_const (show (0 : ℝ) < ε / 2 by positivity)] with T hbT hT hhead
  have htail : ‖∫ t in b..T, f t‖ ≤ (ε / 2) * T := calc
    _ ≤ (ε / 2) * |T - b| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => by
        rw [uIoc_of_le hbT] at ht
        exact (hR t ((le_max_right a R).trans ht.1.le)).le)
    _ ≤ _ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hbT)]
      exact mul_le_mul_of_nonneg_left (sub_le_self _ hb) (by positivity)
  calc
    ‖(∫ t in a..T, f t) / T‖ = ‖∫ t in a..T, f t‖ / T := by
      rw [norm_div, Real.norm_of_nonneg hT.le]
    _ ≤ (C + (ε / 2) * T) / T := by
      apply div_le_div_of_nonneg_right _ hT.le
      rw [← intervalIntegral.integral_add_adjacent_intervals (hi le_rfl hab) (hi hab hbT)]
      exact (norm_add_le _ _).trans (add_le_add_right htail C)
    _ = C / T + ε / 2 := by rw [add_div, mul_div_cancel_right₀ _ hT.ne']
    _ < ε := by linarith

private lemma completeDensity_add_primeLogDensity {t : ℝ} (ht : cutoff ≤ t) :
    completeDensity t + primeLogDensity t =
      -(Real.sqrt (Real.exp t) * (Q (Real.exp t) - primeTail (Real.exp t))) := by
  have hs := (Real.sqrt_pos.mpr (Real.exp_pos t)).ne'
  have hfactor : Real.exp t / Real.sqrt (Real.exp t) = Real.sqrt (Real.exp t) := by
    apply (div_eq_iff hs).2
    rw [← pow_two, Real.sq_sqrt (Real.exp_nonneg t)]
  calc
    _ = -(Real.exp t / Real.sqrt (Real.exp t) * (Q (Real.exp t) - primeTail (Real.exp t))) := by
      rw [completeDensity_eq ht, primeLogDensity]
      ring
    _ = _ := by rw [hfactor]

/-- Under RH, the actual signed theta-tail primitive has logarithmic slope `-2`. -/
private theorem signedPrimePrimitive_slope_of_rh (hRH : RiemannHypothesis) :
    Tendsto (fun T : ℝ => signedPrimePrimitive T / T) atTop (𝓝 (-2 : ℝ)) := by
  let reSeries (t : ℝ) := (normalizedActualZeroSeries t).re
  let residual (t : ℝ) := primeLogDensity t + reSeries t + 2
  have hSeries : Continuous reSeries :=
    Complex.continuous_re.comp normalizedActualZeroSeries_continuous
  have hRem : Tendsto (fun t => completeDensity t - reSeries t) atTop (𝓝 0) := by
    simpa only [completeDensity, RHSharpActualEnvelope.G, reSeries, normalizedActualZeroSeries,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      RHSharpActualEnvelope.G_sub_normalized_actualH_tendsto_zero
  have hBias : Tendsto (fun t : ℝ =>
      Real.sqrt (Real.exp t) * (Q (Real.exp t) - primeTail (Real.exp t))) atTop (𝓝 2) :=
    prime_power_window_correction.1.comp Real.tendsto_exp_atTop
  have hResidual : Tendsto residual atTop (𝓝 0) := by
    have h : Tendsto (fun t : ℝ =>
        2 - Real.sqrt (Real.exp t) * (Q (Real.exp t) - primeTail (Real.exp t)) -
          (completeDensity t - reSeries t)) atTop (𝓝 0) := by
      simpa only [sub_self, sub_zero] using
        ((tendsto_const_nhds (x := (2 : ℝ))).sub hBias).sub hRem
    apply h.congr'
    filter_upwards [eventually_ge_atTop cutoff] with t ht
    dsimp only [residual]
    linarith [completeDensity_add_primeLogDensity ht]
  have hMean := integral_average_tendsto_zero cutoff_nonneg
    ((primeLogDensity_continuousOn.add hSeries.continuousOn).add continuousOn_const) hResidual
  have hZero := normalizedActualZeroSeries_re_average hRH
  have hConst : Tendsto (fun T : ℝ => (T - cutoff) * 2 / T) atTop (𝓝 2) := by
    have hdiv : Tendsto (fun T : ℝ => (cutoff * 2) / T) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul (cutoff * 2)
    have h : Tendsto (fun T : ℝ => 2 - (cutoff * 2) / T) atTop (𝓝 2) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (2 : ℝ))).sub hdiv
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    field_simp [hT.ne']
  have hSlope : Tendsto (fun T : ℝ =>
      (∫ t in cutoff..T, residual t) / T -
        (∫ t in cutoff..T, reSeries t) / T - (T - cutoff) * 2 / T)
      atTop (𝓝 (-2 : ℝ)) := by
    simpa only [sub_self, zero_sub, residual, reSeries, Pi.add_apply] using
      (hMean.sub hZero).sub hConst
  apply hSlope.congr'
  filter_upwards [eventually_ge_atTop cutoff] with T hT
  have hiP : IntervalIntegrable primeLogDensity volume cutoff T :=
    (primeLogDensity_continuousOn.mono (fun _ ht => (uIcc_of_le hT ▸ ht).1)).intervalIntegrable
  have hiZ : IntervalIntegrable reSeries volume cutoff T := hSeries.intervalIntegrable _ _
  rw [signedPrimePrimitive_log hT]
  dsimp only [residual]
  rw [intervalIntegral.integral_add (hiP.add hiZ) intervalIntegrable_const,
    intervalIntegral.integral_add hiP hiZ, intervalIntegral.integral_const, smul_eq_mul]
  ring

end SignedPrimePrimitiveSlope


private lemma eventually_anchor_5040 :
    (fun T : ℝ => signedPrimePrimitive T / T) =ᶠ[atTop]
      (fun T : ℝ =>
        (∫ x in (5040 : ℝ)..Real.exp T, primeTail x / Real.sqrt x) / T +
          (∫ x in 2..(5040 : ℝ), primeTail x / Real.sqrt x) / T) := by
  filter_upwards [eventually_ge_atTop (Real.log 5040)] with T hT
  rw [signedPrimePrimitive_eq_from_5040 hT, add_div, add_comm]

/-- RH is equivalent to slope minus two for the signed actual theta-tail integral
starting at 5040. The integral uses the prime count and no prime-power terms. -/
theorem rh_iff_signedPrimePrimitive_slope_from_5040 :
    RiemannHypothesis ↔
      Tendsto (fun T : ℝ =>
        (∫ x in (5040 : ℝ)..Real.exp T, primeTail x / Real.sqrt x) / T)
        atTop (𝓝 (-2 : ℝ)) := by
  let K : ℝ := ∫ x in 2..(5040 : ℝ), primeTail x / Real.sqrt x
  let F : ℝ → ℝ := fun T =>
    (∫ x in (5040 : ℝ)..Real.exp T, primeTail x / Real.sqrt x) / T
  have hc : Tendsto (fun T : ℝ => K / T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul K
  have heq : (fun T : ℝ => signedPrimePrimitive T / T) =ᶠ[atTop]
      (fun T : ℝ => F T + K / T) := eventually_anchor_5040
  constructor
  · intro hRH
    have hs := (signedPrimePrimitive_slope_of_rh hRH).congr' heq
    have hdiff := hs.sub hc
    simpa only [add_sub_cancel_right, sub_zero] using hdiff
  · intro h
    have hs : Tendsto (fun T : ℝ => signedPrimePrimitive T / T) atTop (𝓝 (-2 : ℝ)) :=
      (show Tendsto (fun T : ℝ => F T + K / T) atTop (𝓝 (-2 : ℝ)) by
        simpa only [add_zero] using h.add hc).congr' heq.symm
    have hg : signedPrimePrimitive =O[atTop] (fun T : ℝ => T) :=
      isBigO_of_div_tendsto_nhds
        ((eventually_gt_atTop (0 : ℝ)).mono fun _ ht hz => (ht.ne' hz).elim) (-2) hs
    apply riemannHypothesis_of_signedPrimePrimitive_polynomial (m := 1)
    refine hg.trans (Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    simpa only [pow_one, one_mul, Real.norm_eq_abs, abs_of_nonneg hT,
      abs_of_nonneg (show 0 ≤ (1 : ℝ) + T by positivity)] using
      le_add_of_nonneg_left (zero_le_one' ℝ)

private lemma completePrimitive_unconditional_growth :
    HasExponentBound 1 completePrimitive := by
  let error (x : ℝ) := (Chebyshev.psi x - x) / x ^ 2
  let C : ℝ := ∫ x in Ioi (1 : ℝ), ‖error x‖
  have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hD (t : ℝ) (ht : cutoff ≤ t) : ‖completeDensity t‖ ≤ C * Real.exp (t / 2) := by
    have htwo := two_le_exp_of_cutoff_le ht
    have hone : 1 ≤ Real.exp t := by linarith
    have hQ' : Q (Real.exp t) = ∫ x in Ioi (Real.exp t), error x := rfl
    have hnorm : ‖Q (Real.exp t)‖ ≤ C := by
      rw [hQ']
      exact (norm_integral_le_integral_norm _).trans
        (setIntegral_mono_set chebyshev_error_kernel_integrable.norm
          (ae_of_all _ fun _ => norm_nonneg _) (Filter.Eventually.of_forall
            (Ioi_subset_Ioi hone)))
    have he : Real.exp t / Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
      rw [← Real.exp_half, ← Real.exp_sub]
      congr 1
      ring
    rw [completeDensity_eq ht, norm_neg, div_mul_eq_mul_div, mul_div_assoc, he,
      norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right hnorm (Real.exp_pos _).le
  intro ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop cutoff] with T hT
  have hcont : Continuous (fun t : ℝ => C * Real.exp (t / 2)) := by fun_prop
  have hint : (∫ t in cutoff..T, C * Real.exp (t / 2)) =
      2 * C * Real.exp (T / 2) - 2 * C * Real.exp (cutoff / 2) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _
      convert ((Real.hasDerivAt_exp (t / 2)).comp t
        ((hasDerivAt_id t).div_const 2)).const_mul (2 * C) using 1
      · simp only [Function.comp_apply, id_eq]
      · ring
    · exact hcont.intervalIntegrable _ _
  rw [completePrimitive]
  calc
    _ ≤ ∫ t in cutoff..T, ‖completeDensity t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hT
    _ ≤ ∫ t in cutoff..T, C * Real.exp (t / 2) :=
      intervalIntegral.integral_mono_on hT
        (completeDensity_continuous.norm.intervalIntegrable _ _)
        (hcont.intervalIntegrable _ _) (fun t ht => hD t ht.1)
    _ ≤ 2 * C * Real.exp (T / 2) := by
      rw [hint]
      exact sub_le_self _ (by positivity)
    _ ≤ 2 * C * Real.exp ((1 + ε - 1 / 2) * T) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by positivity)
      nlinarith [mul_nonneg hε.le (cutoff_nonneg.trans hT)]

private lemma affine_damped_integrable (A B : ℝ) {τ d : ℝ} (hτ : 0 ≤ τ) (hd : 0 < d) :
    IntegrableOn (fun t : ℝ => Real.exp (-d * t) * (A * t + B)) (Ioi τ) := by
  have hlin : IntegrableOn (fun t : ℝ => t * Real.exp (-d * t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := d)
        (by norm_num) one_pos hd)
  have hi : IntegrableOn
      (fun t : ℝ => A * (t * Real.exp (-d * t)) + B * Real.exp (-d * t)) (Ioi τ) :=
    ((hlin.mono_set (Ioi_subset_Ioi hτ)).const_mul A).add
      ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd) τ).const_mul B)
  refine hi.congr_fun (fun t _ => ?_) measurableSet_Ioi
  dsimp only [Pi.add_apply]
  ring

private lemma sub_half_re (s : ℂ) : (s - 1 / 2).re = s.re - 1 / 2 := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl]
  simp only [Complex.sub_re, Complex.ofReal_re]

private lemma affine_kernel_integrable (A B : ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (EulerPoleObstruction.kernel (fun t => A * t + B) (s - 1 / 2)) (Ioi τ) := by
  apply (integrable_norm_iff (kernel_continuous (by fun_prop) _).aestronglyMeasurable).mp
  convert (affine_damped_integrable A B hτ (sub_pos.mpr hs)).norm using 1
  funext t
  rw [kernel_norm, sub_half_re, norm_mul, Real.norm_eq_abs (Real.exp _),
    abs_of_pos (Real.exp_pos _)]

private def affineLaplace (A B τ : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi τ, EulerPoleObstruction.kernel (fun t => A * t + B) (s - 1 / 2) t

private lemma affineLaplace_analytic (A B : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    AnalyticOnNhd ℂ (affineLaplace A B τ) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  change 1 / 2 < s.re at hs
  let d : ℝ := (s.re - 1 / 2) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  let g (t : ℝ) : ℝ := Real.exp (-d * t) * (A * t + B)
  have hg : IntegrableOn g (Ioi τ) := affine_damped_integrable A B hτ hd
  let shift (z : ℂ) : ℂ := (z - 1 / 2) - (d : ℂ)
  have hf : affineLaplace A B τ =
      (fun z => ∫ t in Ioi τ, EulerPoleObstruction.kernel g z t) ∘ shift := by
    funext z
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [shift, g, EulerPoleObstruction.kernel, Complex.ofReal_mul,
      Complex.ofReal_exp, Complex.ofReal_neg, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hf]
  have hpos : 0 < (shift s).re := by
    dsimp only [shift]
    rw [Complex.sub_re, sub_half_re, Complex.ofReal_re]
    dsimp [d]
    linarith
  exact (EulerPoleObstruction.tail_analytic hg hτ (shift s) hpos).comp
    (f := shift) (x := s) ((analyticAt_id.sub analyticAt_const).sub analyticAt_const)

private def primitiveContinuation (s : ℂ) : ℂ :=
  (CompleteMangoldtRealRegular.continued s - completeHead s) / (s - 1 / 2)

private lemma primitiveContinuation_eq {s : ℂ} (hs : 1 < s.re) :
    primitiveContinuation s = primitiveLaplace s := by
  have hn : s - 1 / 2 ≠ 0 := Complex.ne_zero_of_re_pos (by rw [sub_half_re]; linarith)
  apply (div_eq_iff hn).mpr
  rw [CompleteMangoldtRealRegular.continuation.2.2 s hs,
    ← continuedTransform_eq le_rfl completePrimitive_unconditional_growth hs]
  dsimp [continuedTransform]
  ring

/-- A single affine majorant of a nonzero multiple of the complete primitive
suffices to continue the complete Mangoldt transform across the full right half-strip. -/
private theorem complete_transform_of_one_sided_bound {c A B : ℝ} (hc : c ≠ 0)
    (h : ∀ᶠ t in atTop, c * completePrimitive t ≤ A * t + B) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re → L s = CompleteMangoldtLaurent.transform s := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp h
  let τ := max cutoff R
  have hcutτ : cutoff ≤ τ := le_max_left _ _
  have hτ : 0 ≤ τ := cutoff_nonneg.trans hcutτ
  let w (t : ℝ) : ℝ := Real.exp (-(2 - 1 / 2) * t) * (A * t + B - c * completePrimitive t)
  let μ : Measure ℝ := (volume.restrict (Ioi τ)).withDensity (fun t => ENNReal.ofReal (w t))
  have hw : IntegrableOn w (Ioi τ) := by
    have hK := (damped_primitive completePrimitive_unconditional_growth
      (s := (2 : ℂ)) (by norm_num)).1
    have hcast : EulerPoleObstruction.kernel completePrimitive ((2 : ℂ) - 1 / 2) =
        (fun t : ℝ => ((Real.exp (-(2 - 1 / 2) * t) * completePrimitive t : ℝ) : ℂ)) := by
      funext t
      simp only [EulerPoleObstruction.kernel, Complex.ofReal_mul, Complex.ofReal_exp,
        Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_ofNat]
    rw [hcast] at hK
    have hF := (IntegrableOn.iff_ofReal.mpr hK).mono_set (Ioi_subset_Ioi hcutτ)
    have hi : IntegrableOn (fun t : ℝ =>
        Real.exp (-(2 - 1 / 2) * t) * (A * t + B) -
          c * (Real.exp (-(2 - 1 / 2) * t) * completePrimitive t)) (Ioi τ) :=
      (affine_damped_integrable A B hτ (by norm_num : 0 < (2 : ℝ) - 1 / 2)).sub
        (hF.const_mul c)
    refine hi.congr_fun (fun t _ => ?_) measurableSet_Ioi
    dsimp only [w, Pi.sub_apply]
    ring
  have hwpos : ∀ᵐ t ∂volume.restrict (Ioi τ), 0 ≤ w t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (hR t
      ((le_max_right cutoff R).trans ht.le)))
  let hμ : IsFiniteMeasure μ :=
    isFiniteMeasure_withDensity ((hasFiniteIntegral_iff_ofReal hwpos).mp hw.hasFiniteIntegral).ne
  have hX : ∀ᵐ t ∂μ, 0 ≤ id t := by
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hτ.trans ht.le
  have hb : Integrable (fun t : ℝ => Real.exp (-(0 : ℝ) * id t)) μ := by
    simp only [neg_zero, zero_mul, Real.exp_zero]
    exact integrable_const (μ := μ) (1 : ℝ)
  let P (s : ℂ) := EulerPoleObstruction.finiteHead completePrimitive cutoff τ (s - 1 / 2)
  have hP (s : ℂ) : AnalyticAt ℂ P s := by
    have he := EulerPoleObstruction.finiteHead_entire
      (completePrimitive_continuous.integrableOn_Icc (a := cutoff) (b := τ)
        |>.mono_set Ioc_subset_Icc_self)
    exact (he.analyticAt (s - 1 / 2)).comp
      (f := fun z : ℂ => z - 1 / 2) (x := s) (analyticAt_id.sub analyticAt_const)
  have hHead (s : ℂ) : AnalyticAt ℂ completeHead s :=
    (EulerPoleObstruction.finiteHead_entire
      (U_exp_continuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self)).analyticAt s
  have hden (s : ℂ) : AnalyticAt ℂ (fun z : ℂ => z - 1 / 2) s :=
    analyticAt_id.sub analyticAt_const
  have hden_ne {s : ℂ} (hs : 1 / 2 < s.re) : s - 1 / 2 ≠ 0 :=
    Complex.ne_zero_of_re_pos (by rw [sub_half_re]; linarith)
  let K := affineLaplace A B τ
  have hK : AnalyticOnNhd ℂ K {s : ℂ | 1 / 2 < s.re} := affineLaplace_analytic A B hτ
  let shift (z : ℂ) := z + 2
  have hshift (z : ℂ) : AnalyticAt ℂ shift z := analyticAt_id.add analyticAt_const
  let H (z : ℂ) := K (shift z) - (c : ℂ) * (primitiveContinuation (shift z) - P (shift z))
  have hHm : MeromorphicOn H {z | (1 / 2 : ℝ) - 2 < z.re} := by
    intro z hz
    change (1 / 2 : ℝ) - 2 < z.re at hz
    have hs : 1 / 2 < (shift z).re := by
      simp [shift, Complex.add_re]
      linarith
    have hRe : 0 < (shift z).re := by linarith
    have hm : MeromorphicAt primitiveContinuation (shift z) :=
      ((CompleteMangoldtRealRegular.continuation.1 _ hRe).sub
        (hHead _).meromorphicAt).div (hden _).meromorphicAt
    have hc' : AnalyticAt ℂ (fun _ : ℂ => (c : ℂ)) (shift z) := analyticAt_const
    exact ((hK _ hs).meromorphicAt.sub (hc'.meromorphicAt.mul
      (hm.sub (hP _).meromorphicAt))).comp_analyticAt (hshift z)
  have hHa (x : ℝ) (hx : (1 / 2 : ℝ) - 2 < x) : AnalyticAt ℂ H (x : ℂ) := by
    have hs : 1 / 2 < x + 2 := by linarith
    have he : shift (x : ℂ) = ((x + 2 : ℝ) : ℂ) := by simp [shift]
    have hp : AnalyticAt ℂ primitiveContinuation (shift (x : ℂ)) := by
      apply ((?_ : AnalyticAt ℂ CompleteMangoldtRealRegular.continued (shift (x : ℂ))).sub
        (hHead _)).div (hden _) (hden_ne (by simpa [he] using hs))
      rw [he]
      exact CompleteMangoldtRealRegular.continuation.2.1 _ (by linarith)
    exact ((hK _ (by simpa [he] using hs)).sub
      (analyticAt_const.mul (hp.sub (hP _)))).comp
        (f := shift) (x := (x : ℂ)) (hshift _)
  let M (z : ℂ) := ProbabilityTheory.complexMGF id μ (-z)
  have hmatch (z : ℂ) (hs : 1 < (shift z).re) : H z = M z := by
    have hA := affine_kernel_integrable A B hτ (show 1 / 2 < (shift z).re by linarith)
    have hFull := (damped_primitive completePrimitive_unconditional_growth hs).1
    have hTail := hFull.mono_set (Ioi_subset_Ioi hcutτ)
    have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hFull.mono_set Ioc_subset_Ioi_self) hTail
    rw [Ioc_union_Ioi_eq_Ioi hcutτ] at hsplit
    change primitiveLaplace (shift z) = P (shift z) +
      (∫ t in Ioi τ, EulerPoleObstruction.kernel completePrimitive (shift z - 1 / 2) t) at hsplit
    calc
      H z = (∫ t in Ioi τ,
          EulerPoleObstruction.kernel (fun t => A * t + B) (shift z - 1 / 2) t -
          (c : ℂ) * EulerPoleObstruction.kernel completePrimitive (shift z - 1 / 2) t) := by
        dsimp only [H]
        rw [primitiveContinuation_eq hs, hsplit,
          integral_sub hA (hTail.const_mul (c : ℂ)), integral_const_mul]
        simp only [K, affineLaplace, add_sub_cancel_left]
      _ = M z := by
        dsimp only [M, ProbabilityTheory.complexMGF, μ]
        rw [integral_withDensity_eq_integral_toReal_smul₀ hw.aemeasurable.ennreal_ofReal
            (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
        apply integral_congr_ae
        filter_upwards [hwpos] with t ht
        simp only [ENNReal.toReal_ofReal ht, id_eq, Complex.real_smul, w,
          EulerPoleObstruction.kernel, Complex.ofReal_mul, Complex.ofReal_sub,
          Complex.ofReal_add, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_div,
          Complex.ofReal_ofNat, Complex.ofReal_one]
        have hexp : Complex.exp (-(((2 : ℂ) - 1 / 2)) * (t : ℂ)) *
            Complex.exp (-z * (t : ℂ)) = Complex.exp (-(shift z - 1 / 2) * (t : ℂ)) := by
          rw [← Complex.exp_add]
          congr 1
          dsimp [shift]
          ring
        rw [← hexp]
        ring
  have hbase : 1 < (shift (1 : ℂ)).re := by norm_num [shift]
  have hAgree : H =ᶠ[𝓝 (1 : ℂ)] M := by
    have hopen : IsOpen {z : ℂ | 1 < (shift z).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp
        (show Continuous (fun z : ℂ => z + 2) by fun_prop))
    filter_upwards [hopen.mem_nhds hbase] with z hz
    exact hmatch z hz
  obtain ⟨_, hM, _⟩ :=
    PositiveLaplaceContinuation.integrable_and_analytic_of_meromorphic_continuation
      (X := id) measurable_id.aemeasurable hX hb hHm (fun x hx _ => hHa x hx)
      (z₀ := (1 : ℂ)) (by norm_num) (by norm_num) hAgree
  let unshift (s : ℂ) := s - 2
  let L (s : ℂ) := completeHead s + (s - 1 / 2) * (P s + (K s - M (unshift s)) / (c : ℂ))
  refine ⟨L, ?_, ?_⟩
  · intro s hs
    change 1 / 2 < s.re at hs
    have hu : (1 / 2 : ℝ) - 2 < (unshift s).re := by
      simp [unshift, Complex.sub_re]
      linarith
    have hm := (hM (unshift s) hu).comp (f := unshift) (x := s)
      (analyticAt_id.sub analyticAt_const)
    exact (hHead s).add ((hden s).mul ((hP s).add
      (((hK s hs).sub hm).div analyticAt_const (Complex.ofReal_ne_zero.mpr hc))))
  · intro s hs
    have hshift_s : shift (unshift s) = s := sub_add_cancel s 2
    have hm := hmatch (unshift s) (by rwa [hshift_s])
    change K (shift (unshift s)) - (c : ℂ) *
      (primitiveContinuation (shift (unshift s)) - P (shift (unshift s))) = M (unshift s) at hm
    rw [hshift_s, primitiveContinuation_eq hs] at hm
    rw [← continuedTransform_eq le_rfl completePrimitive_unconditional_growth hs]
    dsimp only [L, continuedTransform]
    rw [← hm]
    field_simp [Complex.ofReal_ne_zero.mpr hc]
    ring

private theorem rh_of_completePrimitive_one_sided_bound {c A B : ℝ} (hc : c ≠ 0)
    (h : ∀ᶠ t in atTop, c * completePrimitive t ≤ A * t + B) :
    RiemannHypothesis := by
  obtain ⟨L, hL, hMatch⟩ := complete_transform_of_one_sided_bound hc h
  let G := odeCoefficient L
  let S : Set ℂ := {s | 1 / 2 < s.re}
  have hS : IsOpen S := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected S := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have hζ : AnalyticOnNhd ℂ riemannZeta₁ S :=
    fun s _ => differentiable_riemannZeta₁.analyticAt s
  have hG : AnalyticOnNhd ℂ G S := by
    intro s hs
    have hlinear : AnalyticAt ℂ
        (fun z : ℂ => ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) * z - 1) s :=
      (analyticAt_const.mul analyticAt_id).sub analyticAt_const
    exact hlinear.sub ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul (hL s hs))
  have htwo : 1 < (2 : ℂ).re := by norm_num
  have htwo1 : (2 : ℂ) ≠ 1 := by norm_num
  have hbase : riemannZeta₁ 2 ≠ 0 := by
    rw [zetaOne_eq htwo1]
    exact mul_ne_zero (sub_ne_zero.mpr htwo1) (riemannZeta_ne_zero_of_one_lt_re htwo)
  have hlocal : deriv riemannZeta₁ =ᶠ[𝓝 (2 : ℂ)] (fun s => G s * riemannZeta₁ s) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds htwo] with s hs
    exact zetaOne_is_solution hs (hMatch s hs)
  have hfree := (local_logarithmic_equation_zero_free hS hconn hζ hG
    (show (2 : ℂ) ∈ S by norm_num [S]) hbase hlocal).2
  apply golden_right_half_strip_implies_rh
  intro ρ hρ hright _
  have hρ1 : ρ ≠ 1 := fun he => riemannZeta_one_ne_zero (he ▸ hρ)
  exact hfree ρ hright (by rw [zetaOne_eq hρ1, hρ, mul_zero])

/-- Either eventual affine bound on the signed actual theta-tail integral
starting at 5040 is equivalent to the Riemann hypothesis. -/
theorem rh_iff_signedPrimePrimitive_affine_bounds_from_5040 :
    (RiemannHypothesis ↔ ∃ A B : ℝ, ∀ᶠ T in atTop,
      (∫ x in (5040 : ℝ)..Real.exp T, primeTail x / Real.sqrt x) ≤ A * T + B) ∧
    (RiemannHypothesis ↔ ∃ A B : ℝ, ∀ᶠ T in atTop,
      A * T + B ≤ (∫ x in (5040 : ℝ)..Real.exp T, primeTail x / Real.sqrt x)) := by
  let F (T : ℝ) := ∫ x in (5040 : ℝ)..Real.exp T, primeTail x / Real.sqrt x
  let K : ℝ := ∫ x in 2..(5040 : ℝ), primeTail x / Real.sqrt x
  have hRHBounds (hRH : RiemannHypothesis) :
      ∀ᶠ T in atTop, -3 * T ≤ F T ∧ F T ≤ -T := by
    have hSlope := rh_iff_signedPrimePrimitive_slope_from_5040.mp hRH
    change Tendsto (fun T => F T / T) atTop (𝓝 (-2 : ℝ)) at hSlope
    have hlow : Ioi (-3 : ℝ) ∈ 𝓝 (-2 : ℝ) := Ioi_mem_nhds (by norm_num)
    have hupp : Iio (-1 : ℝ) ∈ 𝓝 (-2 : ℝ) := Iio_mem_nhds (by norm_num)
    filter_upwards [hSlope.eventually hlow, hSlope.eventually hupp,
      eventually_gt_atTop (0 : ℝ)] with T hl hu ht
    exact ⟨(lt_div_iff₀ ht).mp hl |>.le,
      (div_lt_iff₀ ht).mp hu |>.le.trans_eq (neg_one_mul T)⟩
  obtain ⟨D, _, hD⟩ := primitive_prime_power_bound
  have herror : ∀ᶠ T in atTop,
      -(D * T) ≤ completePrimitive T + (K + F T) ∧
        completePrimitive T + (K + F T) ≤ D * T := by
    filter_upwards [eventually_ge_atTop cutoff, eventually_ge_atTop (Real.log 5040)] with T hc ha
    have he := hD T hc
    rw [signedPrimePrimitive_eq_from_5040 ha, Real.norm_eq_abs] at he
    exact abs_le.mp he
  constructor
  · constructor
    · exact fun h => ⟨-1, 0, (hRHBounds h).mono fun T ht => by simpa using ht.2⟩
    · rintro ⟨A, B, h⟩
      apply rh_of_completePrimitive_one_sided_bound
        (c := -1) (A := A + D) (B := B + K) (by norm_num)
      filter_upwards [h, herror] with T ht he
      change F T ≤ A * T + B at ht
      linarith [he.1]
  · constructor
    · exact fun h => ⟨-3, 0, (hRHBounds h).mono fun T ht => by simpa using ht.1⟩
    · rintro ⟨A, B, h⟩
      apply rh_of_completePrimitive_one_sided_bound
        (c := 1) (A := D - A) (B := -B - K) one_ne_zero
      filter_upwards [h, herror] with T ht he
      change A * T + B ≤ F T at ht
      linarith [he.2]

#print axioms zeta_zero_re_le_of_signedPrimePrimitive_exponent
#print axioms rh_iff_signedPrimePrimitive_slope_from_5040
#print axioms rh_iff_signedPrimePrimitive_affine_bounds_from_5040

end D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveCriterion

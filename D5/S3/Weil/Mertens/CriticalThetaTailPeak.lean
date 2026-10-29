/- GID: D5/S3/Weil/Mertens/CriticalThetaTailPeak
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/CriticalThetaTailPeak
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: Critical-exponent amplitude of the actual signed theta tail. -/

import D5.S3.Weil.Mertens.ActualThetaTailLaplace
import D5.S3.Analytic.Laplace.PositiveEulerContinuation
import D5.S3.Analytic.Isolation.RiemannZetaPositiveRealSign
import Mathlib.Probability.Moments.ComplexMGF

/-! Genuine positive moments and the signed theta Euler equation. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology

namespace D5.S3.Weil.Mertens.CriticalThetaTailPeak

private def moment (μ : Measure ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ u, (u : ℂ) ^ n * Complex.exp (-z * (u : ℂ)) ∂μ

private def laplace (μ : Measure ℝ) (z : ℂ) : ℂ := complexMGF id μ (-z)

private theorem interior_of_halfplane {μ : Measure ℝ} {a : ℝ}
    (hi : ∀ x : ℝ, a < x → Integrable (fun u : ℝ => Real.exp (-x * u)) μ)
    {z : ℂ} (hz : a < z.re) : (-z).re ∈ interior (integrableExpSet id μ) := by
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (isOpen_Iio.mem_nhds
    (show (-z).re ∈ Iio (-a) by simp only [mem_Iio, neg_re]; linarith))
  intro x hx
  simpa only [integrableExpSet, mem_ofPred_eq, id_eq, neg_neg] using
    hi (-x) (by change x < -a at hx; linarith)

private theorem moment_hasDeriv {μ : Measure ℝ} {a : ℝ}
    (hi : ∀ x : ℝ, a < x → Integrable (fun u : ℝ => Real.exp (-x * u)) μ)
    (n : ℕ) {z : ℂ} (hz : a < z.re) :
    HasDerivAt (moment μ n) (-moment μ (n + 1) z) z := by
  have hd := (hasDerivAt_integral_pow_mul_exp
    (interior_of_halfplane hi hz) n).comp z (hasDerivAt_id z).neg
  convert hd using 1
  · funext w
    simp only [moment, Function.comp_def, id_eq, neg_mul]
  · simp [moment]

private theorem laplace_deriv {μ : Measure ℝ} {a : ℝ}
    (hi : ∀ x : ℝ, a < x → Integrable (fun u : ℝ => Real.exp (-x * u)) μ)
    {z : ℂ} (hz : a < z.re) : deriv (laplace μ) z = -moment μ 1 z := by
  have he : laplace μ = moment μ 0 := by ext z; simp [laplace, moment, complexMGF]
  rw [he]
  exact (moment_hasDeriv hi 0 hz).deriv

private theorem laplace_second {μ : Measure ℝ} {a : ℝ}
    (hi : ∀ x : ℝ, a < x → Integrable (fun u : ℝ => Real.exp (-x * u)) μ)
    {z : ℂ} (hz : a < z.re) : deriv (deriv (laplace μ)) z = moment μ 2 z := by
  have he : deriv (laplace μ) =ᶠ[𝓝 z] fun w => -moment μ 1 w := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
      with w hw using laplace_deriv hi hw
  rw [he.deriv_eq]
  simpa using (moment_hasDeriv hi 1 hz).neg.deriv

private theorem moment_norm_le {μ : Measure ℝ}
    (hpos : ∀ᵐ u ∂μ, 0 ≤ u) (n : ℕ) (z : ℂ) :
    ‖moment μ n z‖ ≤ ∫ u, u ^ n * Real.exp (-z.re * u) ∂μ := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [hpos] with u hu
  simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg hu,
    Complex.norm_exp, mul_re, neg_re, ofReal_re, neg_im, ofReal_im, mul_zero, sub_zero]

private theorem real_moment {μ : Measure ℝ} (n : ℕ) (x : ℝ) :
    moment μ n (x : ℂ) = ((∫ u, u ^ n * Real.exp (-x * u) ∂μ : ℝ) : ℂ) := by
  simp only [moment, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp, ← Complex.ofReal_pow]
  exact (integral_ofReal).symm

private theorem moment_nonneg {μ : Measure ℝ}
    (hpos : ∀ᵐ u ∂μ, 0 ≤ u) (n : ℕ) (x : ℝ) :
    0 ≤ ∫ u, u ^ n * Real.exp (-x * u) ∂μ := by
  apply integral_nonneg_of_ae
  filter_upwards [hpos] with u hu
  exact mul_nonneg (pow_nonneg hu n) (Real.exp_pos _).le



private def density (U : ℝ) (w : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi U)).withDensity (fun u => ENNReal.ofReal (w u))

private theorem density_finite {U : ℝ} {w : ℝ → ℝ}
    (hw : IntegrableOn w (Ioi U)) (hpos : ∀ᵐ u ∂volume.restrict (Ioi U), 0 ≤ w u) :
    IsFiniteMeasure (density U w) := by
  apply isFiniteMeasure_withDensity
  exact ((hasFiniteIntegral_iff_ofReal hpos).mp hw.hasFiniteIntegral).ne

private theorem density_nonneg {U : ℝ} (hU : 0 ≤ U) (w : ℝ → ℝ) :
    ∀ᵐ u ∂density U w, 0 ≤ u := by
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact hU.trans hu.le

private theorem density_laplace {U : ℝ} {w : ℝ → ℝ}
    (hw : IntegrableOn w (Ioi U)) (hpos : ∀ᵐ u ∂volume.restrict (Ioi U), 0 ≤ w u)
    (z : ℂ) :
    laplace (density U w) z =
      ∫ u in Ioi U, Complex.exp (-z * (u : ℂ)) * (w u : ℂ) := by
  rw [laplace, complexMGF, density,
    integral_withDensity_eq_integral_toReal_smul₀ hw.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hpos] with u hu
  simp [ENNReal.toReal_ofReal hu, id_eq, real_smul, mul_comm]

private theorem density_integrable {U : ℝ} {w : ℝ → ℝ}
    (hw : IntegrableOn w (Ioi U)) (hpos : ∀ᵐ u ∂volume.restrict (Ioi U), 0 ≤ w u)
    (p : ℝ → ℝ) :
    Integrable p (density U w) ↔ IntegrableOn (fun u => w u * p u) (Ioi U) := by
  rw [density, integrable_withDensity_iff_integrable_smul₀' hw.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [hpos] with u hu
  simp [ENNReal.toReal_ofReal hu, smul_eq_mul]

private def envelope (σ c : ℝ) (u : ℝ) : ℝ := c * Real.exp (σ * u) / u

private theorem envelope_nonneg {U σ c : ℝ} (hU : 0 < U) (hc : 0 ≤ c) :
    ∀ᵐ u ∂volume.restrict (Ioi U), 0 ≤ envelope σ c u := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact div_nonneg (mul_nonneg hc (Real.exp_pos _).le) (hU.le.trans hu.le)

private theorem envelope_weighted_integrable {U σ c x : ℝ}
    (hU : 0 < U) (hc : 0 ≤ c) (hx : σ < x) :
    IntegrableOn (fun u => envelope σ c u * Real.exp (-x * u)) (Ioi U) := by
  have he := (integrableOn_exp_mul_Ioi (by linarith : σ - x < 0) U).const_mul (c / U)
  apply he.mono'
  · have hm : Measurable (fun u : ℝ => envelope σ c u * Real.exp (-x * u)) := by
      unfold envelope
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hU.trans hu
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (div_nonneg (mul_nonneg hc (Real.exp_pos _).le) hu0.le) (Real.exp_pos _).le)]
    have hi : 1 / u ≤ 1 / U := one_div_le_one_div_of_le hU hu.le
    calc
      envelope σ c u * Real.exp (-x * u) =
          c * Real.exp ((σ - x) * u) * (1 / u) := by
        rw [envelope, sub_mul, Real.exp_sub, Real.exp_neg]
        ring
      _ ≤ c * Real.exp ((σ - x) * u) * (1 / U) :=
        mul_le_mul_of_nonneg_left hi (mul_nonneg hc (Real.exp_pos _).le)
      _ = (c / U) * Real.exp ((σ - x) * u) := by ring

private theorem envelope_integrable {U σ c : ℝ}
    (hU : 0 < U) (hσ : σ < 0) (hc : 0 ≤ c) : IntegrableOn (envelope σ c) (Ioi U) := by
  simpa using envelope_weighted_integrable hU hc hσ

private theorem envelope_exp_integrable {U σ c : ℝ}
    (hU : 0 < U) (hσ : σ < 0) (hc : 0 ≤ c) :
    ∀ x : ℝ, σ < x → Integrable (fun u => Real.exp (-x * u))
      (density U (envelope σ c)) := by
  intro x hx
  exact (density_integrable (envelope_integrable hU hσ hc) (envelope_nonneg hU hc) _).mpr
    (envelope_weighted_integrable hU hc hx)

private theorem envelope_moment_one {U σ c : ℝ}
    (hU : 0 < U) (hσ : σ < 0) (hc : 0 ≤ c) {z : ℂ} (hz : σ < z.re) :
    moment (density U (envelope σ c)) 1 z =
      (c : ℂ) * Complex.exp (-(z - (σ : ℂ)) * (U : ℂ)) / (z - (σ : ℂ)) := by
  rw [moment, density, integral_withDensity_eq_integral_toReal_smul₀
    (envelope_integrable hU hσ hc).aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have he : (fun u : ℝ => (ENNReal.ofReal (envelope σ c u)).toReal •
      ((u : ℂ) ^ 1 * Complex.exp (-z * (u : ℂ)))) =ᵐ[volume.restrict (Ioi U)]
      (fun u => (c : ℂ) * Complex.exp (-(z - (σ : ℂ)) * (u : ℂ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hU.trans hu
    rw [ENNReal.toReal_ofReal (div_nonneg
      (mul_nonneg hc (Real.exp_pos _).le) hu0.le), real_smul, envelope,
      Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_exp]
    have hun : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
    rw [show -(z - (σ : ℂ)) * (u : ℂ) =
      (σ : ℂ) * (u : ℂ) + -z * (u : ℂ) by ring, Complex.exp_add]
    push_cast
    field_simp
  rw [integral_congr_ae he, integral_const_mul,
    integral_exp_mul_complex_Ioi (by simp only [neg_re, sub_re, ofReal_re]; linarith)]
  ring

private theorem envelope_first {U σ c : ℝ}
    (hU : 0 < U) (hσ : σ < 0) (hc : 0 ≤ c) {z : ℂ} (hz : σ < z.re) :
    deriv (laplace (density U (envelope σ c))) z =
      -(c : ℂ) * Complex.exp (-(z - (σ : ℂ)) * (U : ℂ)) / (z - (σ : ℂ)) := by
  rw [laplace_deriv (envelope_exp_integrable hU hσ hc) hz,
    envelope_moment_one hU hσ hc hz]
  ring

private theorem envelope_second {U σ c : ℝ}
    (hU : 0 < U) (hσ : σ < 0) (hc : 0 ≤ c) {z : ℂ} (hz : σ < z.re) :
    deriv (deriv (laplace (density U (envelope σ c)))) z =
      (c : ℂ) * Complex.exp (-(z - (σ : ℂ)) * (U : ℂ)) *
        (1 / (z - (σ : ℂ)) ^ 2 + (U : ℂ) / (z - (σ : ℂ))) := by
  have he : deriv (laplace (density U (envelope σ c))) =ᶠ[𝓝 z]
      fun w => -(c : ℂ) * Complex.exp (-(w - (σ : ℂ)) * (U : ℂ)) / (w - (σ : ℂ)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
      with w hw using envelope_first hU hσ hc hw
  have hn : z - (σ : ℂ) ≠ 0 := by
    intro heq
    have hr := congrArg Complex.re (sub_eq_zero.mp heq)
    simp only [ofReal_re] at hr
    linarith
  rw [he.deriv_eq]
  have hd := ((((hasDerivAt_id z).sub_const (σ : ℂ)).neg.mul_const (U : ℂ)).cexp.const_mul
    (-(c : ℂ))).div ((hasDerivAt_id z).sub_const (σ : ℂ)) hn
  rw [hd.deriv]
  field_simp
  ring

private def euler (F : ℂ → ℂ) (z : ℂ) : ℂ := z * deriv (deriv F) z + 2 * deriv F z

private theorem euler_congr {F G : ℂ → ℂ} {z : ℂ} (he : F =ᶠ[𝓝 z] G) :
    euler F z = euler G z := by
  simp only [euler, he.deriv_eq, he.deriv.deriv_eq]

private theorem euler_sub {F G : ℂ → ℂ} {z : ℂ}
    (hF : AnalyticAt ℂ F z) (hG : AnalyticAt ℂ G z) :
    euler (fun w => F w - G w) z = euler F z - euler G z := by
  have he : deriv (fun w => F w - G w) =ᶠ[𝓝 z] fun w => deriv F w - deriv G w := by
    filter_upwards [hF.eventually_analyticAt, hG.eventually_analyticAt] with w hf hg
    exact deriv_sub hf.differentiableAt hg.differentiableAt
  rw [euler, he.deriv_eq, deriv_sub hF.deriv.differentiableAt hG.deriv.differentiableAt,
    deriv_sub hF.differentiableAt hG.differentiableAt]
  simp only [euler]
  ring

private def boundary (U : ℝ) (z : ℂ) : ℂ :=
  (U : ℂ) ^ 2 * (ActualThetaTailLaplace.f U : ℂ) * Complex.exp (-z * (U : ℂ))

private def forcing (U : ℝ) (z : ℂ) : ℂ :=
  -deriv (ThetaLaplaceContinuation.M U) z + ThetaLaplaceContinuation.M U z + boundary U z

private theorem forcing_meromorphic (U : ℝ) (hU : 0 ≤ U) :
    MeromorphicOn (forcing U) ThetaLaplaceContinuation.D := by
  have hm := (ThetaLaplaceContinuation.theta_laplace_continuation U hU).2.2.2.2.1
  exact (hm.deriv.neg.add hm).add (by intro z hz; exact (by fun_prop :
    AnalyticAt ℂ (boundary U) z).meromorphicAt)

private theorem normalized_zeta_real_ne_zero {x : ℝ} (hx : 0 < x) :
    riemannZeta₁ (x : ℂ) ≠ 0 := by
  by_cases hx1 : x = 1
  · subst x
    simp
  · have hs := D5.S3.Analytic.Isolation.RiemannZetaPositiveRealSign.riemannZeta_ofReal_sign hx hx1
    have hz : riemannZeta (x : ℂ) ≠ 0 := by
      intro hz
      rw [hz] at hs
      rcases hs.2 with h | h <;> simp only [zero_re] at h <;> linarith [h.2]
    intro hn
    apply hz
    rw [riemannZeta_eq_inv_sub_mul (by exact_mod_cast hx1), hn, mul_zero]

private theorem theta_M_real_analytic (U : ℝ) (hU : 0 ≤ U) {x : ℝ}
    (hx : -(1 / 2 : ℝ) < x) : AnalyticAt ℂ (ThetaLaplaceContinuation.M U) (x : ℂ) := by
  obtain ⟨hC, hA, _, _, _, hzero, _⟩ :=
    ThetaLaplaceContinuation.theta_laplace_continuation U hU
  by_cases hx0 : x = 0
  · subst x
    simpa using hzero
  have hn := normalized_zeta_real_ne_zero (by linarith : 0 < 1 + x)
  have hna : AnalyticAt ℂ (logDeriv riemannZeta₁) ((1 + x : ℝ) : ℂ) :=
    (differentiable_riemannZeta₁.analyticAt _).deriv.div
      (differentiable_riemannZeta₁.analyticAt _) hn
  have hcomp : AnalyticAt ℂ (fun z => logDeriv riemannZeta₁ (1 + z)) (x : ℂ) := by
    convert hna.comp (by fun_prop : AnalyticAt ℂ (fun z : ℂ => 1 + z) (x : ℂ)) using 1 <;>
      norm_cast
  have hc : AnalyticAt ℂ (fun z => ThetaLaplaceContinuation.C (1 + z)) (x : ℂ) :=
    (hC (1 + (x : ℂ)) (by simp; linarith)).comp (by fun_prop)
  unfold ThetaLaplaceContinuation.M
  exact (((analyticAt_const.add hcomp).add hc).neg.div (by fun_prop)
    (by intro h; have hr := congrArg Complex.re h; simp at hr; linarith)).sub (hA.analyticAt _)

private theorem forcing_real_analytic (U : ℝ) (hU : 0 ≤ U) {x : ℝ}
    (hx : -(1 / 2 : ℝ) < x) : AnalyticAt ℂ (forcing U) (x : ℂ) := by
  have hm := theta_M_real_analytic U hU hx
  exact (hm.deriv.neg.add hm).add (by unfold boundary; fun_prop)

private theorem actual_euler (U : ℝ) (hU : ActualThetaTailLaplace.u₀ ≤ U)
    {z : ℂ} (hz : 0 < z.re) : euler (ActualThetaTailLaplace.L U) z = forcing U z := by
  have hU0 : 0 ≤ U := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hU
  have hcont := ThetaLaplaceContinuation.theta_laplace_continuation U hU0
  have hqm : ThetaLaplaceContinuation.Q U =ᶠ[𝓝 z] ThetaLaplaceContinuation.M U := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
    exact (hcont.2.2.2.1 w hw).2.1
  have he := ((ActualThetaTailLaplace.actual_theta_tail_laplace_ode).2.2.2.2.2.2.2.2.2 U hU).2 z hz
  simpa only [euler, forcing, boundary, hqm.deriv_eq, hqm.eq_of_nhds] using he.2.2.2

private def envelopeEuler (U σ c : ℝ) (z : ℂ) : ℂ :=
  (c : ℂ) * Complex.exp (-(z - (σ : ℂ)) * (U : ℂ)) *
    (z / (z - (σ : ℂ)) ^ 2 + (z * (U : ℂ) - 2) / (z - (σ : ℂ)))

private theorem envelope_euler {U σ c : ℝ}
    (hU : 0 < U) (hσ : σ < 0) (hc : 0 ≤ c) {z : ℂ} (hz : σ < z.re) :
    euler (laplace (density U (envelope σ c))) z = envelopeEuler U σ c z := by
  rw [euler, envelope_first hU hσ hc hz, envelope_second hU hσ hc hz]
  unfold envelopeEuler
  ring

private theorem envelopeEuler_analytic {U σ c : ℝ} {z : ℂ} (hz : z ≠ (σ : ℂ)) :
    AnalyticAt ℂ (envelopeEuler U σ c) z := by
  have hn : z - (σ : ℂ) ≠ 0 := sub_ne_zero.mpr hz
  unfold envelopeEuler
  fun_prop (disch := positivity)

private theorem zeta_zero_nonreal {ρ : ℂ} (hβ : (1 / 2 : ℝ) < ρ.re)
    (hβ1 : ρ.re < 1) (hz : riemannZeta ρ = 0) : ρ.im ≠ 0 := by
  intro him
  have hr : (ρ.re : ℂ) = ρ := by apply Complex.ext <;> simp [him]
  have hs := D5.S3.Analytic.Isolation.RiemannZetaPositiveRealSign.riemannZeta_ofReal_sign
    (by linarith : 0 < ρ.re) hβ1.ne
  rw [hr, hz] at hs
  rcases hs.2 with h | h <;> simp only [zero_re] at h <;> linarith [h.1, h.2]

private theorem complex_weight_integrable {U : ℝ} {w : ℝ → ℝ} {z : ℂ}
    (hw : AEStronglyMeasurable w (volume.restrict (Ioi U)))
    (hi : IntegrableOn (fun u => w u * Real.exp (-z.re * u)) (Ioi U)) :
    IntegrableOn (fun u => Complex.exp (-z * (u : ℂ)) * (w u : ℂ)) (Ioi U) := by
  have hm : AEStronglyMeasurable
      (fun u : ℝ => Complex.exp (-z * (u : ℂ)) * (w u : ℂ)) (volume.restrict (Ioi U)) := by
    exact (by fun_prop : AEStronglyMeasurable
      (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (volume.restrict (Ioi U))).mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hw)
  apply (integrable_norm_iff hm).mp
  convert hi.norm using 1
  ext u
  simp only [norm_mul, Complex.norm_exp, mul_re, neg_re, ofReal_re, neg_im, ofReal_im,
    mul_zero, sub_zero, norm_real, Real.norm_eq_abs, abs_mul, Real.abs_exp]
  ring

private def gap (σ c : ℝ) (u : ℝ) : ℝ := envelope σ c u - ActualThetaTailLaplace.f u

private theorem actual_tail_integrable {U : ℝ} (hU : ActualThetaTailLaplace.u₀ ≤ U) :
    IntegrableOn ActualThetaTailLaplace.f (Ioi U) :=
  ActualThetaTailLaplace.actual_theta_tail_laplace_ode.2.2.2.2.1.mono_set (Ioi_subset_Ioi hU)

private theorem gap_integrable {U σ c : ℝ} (hU : ActualThetaTailLaplace.u₀ ≤ U)
    (hU0 : 0 < U) (hσ : σ < 0) (hc : 0 ≤ c) : IntegrableOn (gap σ c) (Ioi U) :=
  (envelope_integrable hU0 hσ hc).sub (actual_tail_integrable hU)

private theorem gap_nonneg {U σ c : ℝ}
    (hbound : ∀ u : ℝ, U < u → ActualThetaTailLaplace.f u ≤ envelope σ c u) :
    ∀ᵐ u ∂volume.restrict (Ioi U), 0 ≤ gap σ c u := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact sub_nonneg.mpr (hbound u hu)

private theorem positive_exp_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hpos : ∀ᵐ u ∂μ, 0 ≤ u) {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun u : ℝ => Real.exp (-x * u)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [hpos] with u hu
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) hu)

private theorem gap_laplace_eq {U σ c : ℝ} (hU : ActualThetaTailLaplace.u₀ ≤ U)
    (hU0 : 0 < U) (hσ : σ < 0) (hc : 0 ≤ c)
    (hbound : ∀ u : ℝ, U < u → ActualThetaTailLaplace.f u ≤ envelope σ c u)
    {z : ℂ} (hz : σ < z.re)
    (hfi : IntegrableOn (fun u => ActualThetaTailLaplace.f u * Real.exp (-z.re * u)) (Ioi U)) :
    laplace (density U (gap σ c)) z =
      laplace (density U (envelope σ c)) z - ActualThetaTailLaplace.L U z := by
  rw [density_laplace (gap_integrable hU hU0 hσ hc) (gap_nonneg hbound),
    density_laplace (envelope_integrable hU0 hσ hc) (envelope_nonneg hU0 hc),
    ActualThetaTailLaplace.L]
  simp only [gap, Complex.ofReal_sub, mul_sub]
  rw [integral_sub
    (complex_weight_integrable (envelope_integrable hU0 hσ hc).aestronglyMeasurable
      (envelope_weighted_integrable hU0 hc hz))
    (complex_weight_integrable (actual_tail_integrable hU).aestronglyMeasurable hfi)]

private theorem laplace_analytic {μ : Measure ℝ} {a : ℝ}
    (hi : ∀ x : ℝ, a < x → Integrable (fun u : ℝ => Real.exp (-x * u)) μ) :
    AnalyticOnNhd ℂ (laplace μ) {z | a < z.re} := by
  intro z hz
  exact (analyticAt_complexMGF (interior_of_halfplane hi hz)).comp (analyticAt_id.neg)

private theorem comparison_halfplane {U σ c : ℝ}
    (hU : ActualThetaTailLaplace.u₀ ≤ U) (hU0 : 0 < U)
    (hσ : σ < 0) (hσhalf : -(1 / 2 : ℝ) < σ) (hc : 0 ≤ c)
    (hbound : ∀ u : ℝ, U < u → ActualThetaTailLaplace.f u ≤ envelope σ c u) :
    (∀ x : ℝ, σ < x → Integrable (fun u => Real.exp (-x * u)) (density U (gap σ c))) ∧
    (∀ x : ℝ, σ < x → IntegrableOn
      (fun u => ActualThetaTailLaplace.f u * Real.exp (-x * u)) (Ioi U)) ∧
    AnalyticOnNhd ℂ (ActualThetaTailLaplace.L U) {z | σ < z.re} ∧
    (∀ z : ℂ, σ < z.re → AnalyticAt ℂ (forcing U) z →
      euler (ActualThetaTailLaplace.L U) z = forcing U z) := by
  let μ := density U (gap σ c)
  let K := laplace (density U (envelope σ c))
  let G := laplace μ
  have hgi := gap_integrable hU hU0 hσ hc
  have hgp := gap_nonneg hbound
  letI : IsFiniteMeasure μ := density_finite hgi hgp
  have hpos := density_nonneg hU0.le (gap σ c)
  have hK := laplace_analytic (envelope_exp_integrable hU0 hσ hc)
  have hfi0 : ∀ x : ℝ, 0 < x → IntegrableOn
      (fun u => ActualThetaTailLaplace.f u * Real.exp (-x * u)) (Ioi U) := by
    intro x hx
    apply (actual_tail_integrable hU).mono'
    · exact (actual_tail_integrable hU).aestronglyMeasurable.mul (by fun_prop)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
      apply mul_le_of_le_one_right (abs_nonneg _)
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hx.le.neg
        (hU0.le.trans hu.le))
  have hG0 : ∀ z : ℂ, 0 < z.re → euler G z =
      envelopeEuler U σ c z - forcing U z := by
    intro z hz
    have he : G =ᶠ[𝓝 z] fun w => K w - ActualThetaTailLaplace.L U w := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
        with w hw
      exact gap_laplace_eq hU hU0 hσ hc hbound (lt_trans hσ hw) (hfi0 _ hw)
    rw [euler_congr he, euler_sub (hK z (lt_trans hσ hz))
      (((ActualThetaTailLaplace.actual_theta_tail_laplace_ode).2.2.2.2.2.2.2.2.2 U hU).1 z hz),
      envelope_euler hU0 hσ hc (lt_trans hσ hz), actual_euler U hU hz]
  have hP : AnalyticOnNhd ℂ (envelopeEuler U σ c) {z | σ < z.re} := by
    intro z hz
    apply envelopeEuler_analytic
    intro he
    rw [he, ofReal_re] at hz
    exact lt_irrefl _ hz
  have hRm : MeromorphicOn (fun z => envelopeEuler U σ c z - forcing U z)
      {z | σ < z.re} := hP.meromorphicOn.sub
    (fun z hz => forcing_meromorphic U hU0.le z (lt_trans hσhalf hz))
  have hRa : ∀ x : ℝ, σ < x →
      AnalyticAt ℂ (fun z => envelopeEuler U σ c z - forcing U z) (x : ℂ) := by
    intro x hx
    exact (hP x hx).sub (forcing_real_analytic U hU0.le (lt_trans hσhalf hx))
  obtain ⟨hi, hG⟩ := D5.S3.Analytic.Laplace.PositiveEulerContinuation.integrable_and_analytic_of_euler
    (μ := μ) (X := id) (by fun_prop) hpos hσ hRm hRa hG0
  have hfi : ∀ x : ℝ, σ < x → IntegrableOn
      (fun u => ActualThetaTailLaplace.f u * Real.exp (-x * u)) (Ioi U) := by
    intro x hx
    have hgx := (density_integrable hgi hgp _).mp (hi x hx)
    convert (envelope_weighted_integrable hU0 hc hx).sub hgx using 1
    ext u
    simp only [gap]
    ring
  have heq : ∀ z : ℂ, σ < z.re → ActualThetaTailLaplace.L U z = K z - G z := by
    intro z hz
    have he := gap_laplace_eq hU hU0 hσ hc hbound hz (hfi z.re hz)
    change G z = K z - ActualThetaTailLaplace.L U z at he
    linear_combination -he
  have hL : AnalyticOnNhd ℂ (ActualThetaTailLaplace.L U) {z | σ < z.re} := by
    intro z hz
    apply ((hK z hz).sub (hG z hz)).congr
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
      with w hw using (heq w hw).symm
  refine ⟨hi, hfi, hL, ?_⟩
  let D : ℂ → ℂ := fun z => euler (ActualThetaTailLaplace.L U) z - forcing U z
  have hDm : MeromorphicOn D {z | σ < z.re} := by
    have hm := hL.meromorphicOn
    exact ((analyticOnNhd_id.meromorphicOn.mul hm.deriv.deriv).add
      (analyticOnNhd_const.meromorphicOn.mul hm.deriv)).sub
      (fun z hz => forcing_meromorphic U hU0.le z (lt_trans hσhalf hz))
  have hD1 : meromorphicOrderAt D (1 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with z hz
    exact sub_eq_zero.mpr (actual_euler U hU hz)
  intro z hz hRz
  have htop := hDm.meromorphicOrderAt_eq_top_of_isPreconnected
    (convex_halfSpace_re_gt σ).isPreconnected
    (show σ < (1 : ℂ).re by simp only [one_re]; linarith) hz hD1
  have hDc : ContinuousAt D z := by
    exact ((continuousAt_id.mul (hL z hz).deriv.deriv.continuousAt).add
      ((hL z hz).deriv.continuousAt.const_mul 2)).sub hRz.continuousAt
  have hp : D =ᶠ[𝓝[≠] z] fun _ => 0 := meromorphicOrderAt_eq_top_iff.mp htop
  have he : D z = 0 := tendsto_nhds_unique
    (hDc.tendsto.mono_left nhdsWithin_le_nhds) (tendsto_const_nhds.congr' hp.symm)
  exact sub_eq_zero.mp he

end D5.S3.Weil.Mertens.CriticalThetaTailPeak

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
  exact integral_ofReal

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
    unfold envelope
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (div_nonneg (mul_nonneg hc (Real.exp_pos _).le) hu0.le) (Real.exp_pos _).le)]
    have hi : 1 / u ≤ 1 / U := one_div_le_one_div_of_le hU hu.le
    calc
      c * Real.exp (σ * u) / u * Real.exp (-x * u) =
          c * Real.exp ((σ - x) * u) * (1 / u) := by
        rw [sub_mul, Real.exp_sub, neg_mul, Real.exp_neg]
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
    unfold envelope
    rw [ENNReal.toReal_ofReal (div_nonneg
      (mul_nonneg hc (Real.exp_pos _).le) hu0.le), real_smul,
      Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_exp]
    have hun : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
    rw [show -(z - (σ : ℂ)) * (u : ℂ) =
      (σ : ℂ) * (u : ℂ) + -z * (u : ℂ) by ring, Complex.exp_add]
    push_cast
    field_simp
  rw [integral_congr_ae he, integral_const_mul,
    integral_exp_mul_complex_Ioi (by simp only [neg_re, sub_re, ofReal_re]; linarith)]
  simp only [div_neg]
  ring

private theorem envelope_first {U σ c : ℝ}
    (hU : 0 < U) (hσ : σ < 0) (hc : 0 ≤ c) {z : ℂ} (hz : σ < z.re) :
    deriv (laplace (density U (envelope σ c))) z =
      -(c : ℂ) * Complex.exp (-(z - (σ : ℂ)) * (U : ℂ)) / (z - (σ : ℂ)) := by
  rw [laplace_deriv (envelope_exp_integrable hU hσ hc) hz,
    envelope_moment_one hU hσ hc hz]
  ring

private theorem envelope_analytic {U σ c : ℝ}
    (hU : 0 < U) (hσ : σ < 0) (hc : 0 ≤ c) :
    AnalyticOnNhd ℂ (laplace (density U (envelope σ c))) {z | σ < z.re} := by
  have hd : DifferentiableOn ℂ (laplace (density U (envelope σ c))) {z | σ < z.re} := by
    intro z hz
    have hh := (moment_hasDeriv (envelope_exp_integrable hU hσ hc) 0 hz).differentiableAt
    have he : moment (density U (envelope σ c)) 0 = laplace (density U (envelope σ c)) := by
      ext w
      simp [moment, laplace, complexMGF]
    rw [he] at hh
    exact hh.differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

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
  change HasDerivAt (fun w : ℂ =>
    -(c : ℂ) * Complex.exp (-(w - (σ : ℂ)) * (U : ℂ)) / (w - (σ : ℂ))) _ z at hd
  rw [hd.deriv]
  dsimp only [id_eq, Pi.neg_apply]
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
  rw [euler, he.deriv_eq]
  change z * deriv (deriv F - deriv G) z + 2 * deriv (F - G) z = _
  rw [deriv_sub hF.deriv.differentiableAt hG.deriv.differentiableAt,
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
  exact (hm.deriv.neg.add hm).add (by intro z hz; exact (by unfold boundary; fun_prop :
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
    exact hna.comp_of_eq (by fun_prop : AnalyticAt ℂ (fun z : ℂ => 1 + z) (x : ℂ))
      (by push_cast; ring)
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
  fun_prop (disch := simp [hn])

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
    IntegrableOn (fun u : ℝ => Complex.exp (-z * (u : ℂ)) * (w u : ℂ)) (Ioi U) := by
  have hm : AEStronglyMeasurable
      (fun u : ℝ => Complex.exp (-z * (u : ℂ)) * (w u : ℂ)) (volume.restrict (Ioi U)) := by
    exact (by fun_prop : AEStronglyMeasurable
      (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (volume.restrict (Ioi U))).mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hw)
  apply (integrable_norm_iff hm).mp
  convert hi.norm using 1
  ext u
  simp only [norm_mul, Complex.norm_exp, mul_re, neg_re, ofReal_re, neg_im, ofReal_im,
    mul_zero, sub_zero, norm_real, Real.norm_eq_abs, Real.abs_exp]
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
  exact integral_sub
    (complex_weight_integrable (envelope_integrable hU0 hσ hc).aestronglyMeasurable
      (envelope_weighted_integrable hU0 hc hz))
    (complex_weight_integrable (actual_tail_integrable hU).aestronglyMeasurable hfi)

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
  haveI : IsFiniteMeasure μ := density_finite hgi hgp
  have hpos := density_nonneg hU0.le (gap σ c)
  have hK := envelope_analytic hU0 hσ hc
  have hfi0 : ∀ x : ℝ, 0 < x → IntegrableOn
      (fun u => ActualThetaTailLaplace.f u * Real.exp (-x * u)) (Ioi U) := by
    intro x hx
    apply (actual_tail_integrable hU).norm.mono'
    · exact (actual_tail_integrable hU).aestronglyMeasurable.mul (by fun_prop)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
      apply mul_le_of_le_one_right (abs_nonneg _)
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx.le)
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
    change σ < z.re at hz
    exact (lt_irrefl σ) (by simpa only [he, ofReal_re] using hz)
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
    dsimp only [gap, Pi.sub_apply, id_eq]
    ring
  have heq : ∀ z : ℂ, σ < z.re → ActualThetaTailLaplace.L U z = K z - G z := by
    intro z hz
    have he := gap_laplace_eq hU hU0 hσ hc hbound hz (hfi z.re hz)
    change G z = K z - ActualThetaTailLaplace.L U z at he
    linear_combination he
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



private theorem boundary_moment_limits {μ : Measure ℝ} {U σ c δ : ℝ}
    (hU : 0 < U) (hσ : σ < 0) (hc : 0 ≤ c) (hδ : 0 < δ)
    (hi : ∀ x : ℝ, σ < x → Integrable (fun u : ℝ => Real.exp (-x * u)) μ)
    {S H : ℂ → ℂ} (hS : AnalyticOnNhd ℂ S {z | σ < z.re})
    (heq : ∀ z : ℂ, σ < z.re → laplace μ z =
      laplace (density U (envelope σ c)) z - S z)
    (hH : DifferentiableOn ℂ H (Metric.ball (σ : ℂ) δ))
    (hHS : EqOn H S (D5.S3.Analytic.Laplace.EulerLocalContinuation.rightHalfDisk σ δ)) :
    Tendsto (fun ε : ℝ => ε ^ 2 * ∫ u, u * Real.exp (-(σ + ε) * u) ∂μ)
      (𝓝[Ioi 0] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => ε ^ 2 * ∫ u, u ^ 2 * Real.exp (-(σ + ε) * u) ∂μ)
      (𝓝[Ioi 0] 0) (𝓝 c) := by
  let K := laplace (density U (envelope σ c))
  have hK := envelope_analytic hU hσ hc
  have hG1 : ∀ z : ℂ, σ < z.re → moment μ 1 z = -deriv K z + deriv S z := by
    intro z hz
    have he : laplace μ =ᶠ[𝓝 z] fun w => K w - S w := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
        with w hw using heq w hw
    have hd := he.deriv_eq
    change deriv (laplace μ) z = deriv (K - S) z at hd
    have hs1 : deriv (K - S) z = deriv K z - deriv S z :=
      deriv_sub (hK z hz).differentiableAt (hS z hz).differentiableAt
    rw [laplace_deriv hi hz, hs1] at hd
    linear_combination -hd
  have hG2 : ∀ z : ℂ, σ < z.re → moment μ 2 z = deriv (deriv K) z - deriv (deriv S) z := by
    intro z hz
    have he : deriv (laplace μ) =ᶠ[𝓝 z] fun w => deriv K w - deriv S w := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
      rw [laplace_deriv hi hw, hG1 w hw]
      ring
    have hd := he.deriv_eq
    change deriv (deriv (laplace μ)) z = deriv (deriv K - deriv S) z at hd
    have hs2 : deriv (deriv K - deriv S) z = deriv (deriv K) z - deriv (deriv S) z :=
      deriv_sub (hK z hz).deriv.differentiableAt (hS z hz).deriv.differentiableAt
    rw [laplace_second hi hz, hs2] at hd
    exact hd
  have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[Ioi 0] 0) (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hp : Tendsto (fun ε : ℝ => (σ : ℂ) + (ε : ℂ)) (𝓝[Ioi 0] 0) (𝓝 (σ : ℂ)) := by
    simpa using tendsto_const_nhds.add hε
  have hHa := (hH.analyticOnNhd Metric.isOpen_ball) (σ : ℂ) (Metric.mem_ball_self hδ)
  have hSd : ∀ᶠ ε : ℝ in 𝓝[Ioi 0] 0,
      deriv S ((σ : ℂ) + (ε : ℂ)) = deriv H ((σ : ℂ) + (ε : ℂ)) ∧
      deriv (deriv S) ((σ : ℂ) + (ε : ℂ)) = deriv (deriv H) ((σ : ℂ) + (ε : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with ε hε0 hεδ
    have hεp : 0 < ε := hε0
    have hz : (σ : ℂ) + (ε : ℂ) ∈
        D5.S3.Analytic.Laplace.EulerLocalContinuation.rightHalfDisk σ δ := by
      constructor
      · simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_of_pos hεp] using hεδ
      · change σ < ((σ : ℂ) + (ε : ℂ)).re
        simp only [add_re, ofReal_re]
        linarith
    have ho : IsOpen (D5.S3.Analytic.Laplace.EulerLocalContinuation.rightHalfDisk σ δ) :=
      Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
    have he : S =ᶠ[𝓝 ((σ : ℂ) + (ε : ℂ))] H := by
      filter_upwards [ho.mem_nhds hz] with w hw using (hHS hw).symm
    exact ⟨he.deriv_eq, he.deriv.deriv_eq⟩
  have hS1 : Tendsto (fun ε : ℝ => deriv S ((σ : ℂ) + (ε : ℂ))) (𝓝[Ioi 0] 0)
      (𝓝 (deriv H (σ : ℂ))) :=
    (hHa.deriv.continuousAt.tendsto.comp hp).congr' (hSd.mono fun _ h => h.1.symm)
  have hS2 : Tendsto (fun ε : ℝ => deriv (deriv S) ((σ : ℂ) + (ε : ℂ))) (𝓝[Ioi 0] 0)
      (𝓝 (deriv (deriv H) (σ : ℂ))) :=
    (hHa.deriv.deriv.continuousAt.tendsto.comp hp).congr' (hSd.mono fun _ h => h.2.symm)
  have hS1zero : Tendsto (fun ε : ℝ => (ε : ℂ) ^ 2 * deriv S ((σ : ℂ) + (ε : ℂ)))
      (𝓝[Ioi 0] 0) (𝓝 (0 : ℂ)) := by simpa using (hε.pow 2).mul hS1
  have hS2zero : Tendsto (fun ε : ℝ => (ε : ℂ) ^ 2 * deriv (deriv S) ((σ : ℂ) + (ε : ℂ)))
      (𝓝[Ioi 0] 0) (𝓝 (0 : ℂ)) := by simpa using (hε.pow 2).mul hS2
  have he : Tendsto (fun ε : ℝ => Complex.exp (-(ε : ℂ) * (U : ℂ)))
      (𝓝[Ioi 0] 0) (𝓝 (1 : ℂ)) := by
    simpa [Function.comp_def] using
      (Complex.continuous_exp.tendsto (-(0 : ℂ) * (U : ℂ))).comp (hε.neg.mul_const (U : ℂ))
  have hK1zero : Tendsto (fun ε : ℝ => (ε : ℂ) ^ 2 * deriv K ((σ : ℂ) + (ε : ℂ)))
      (𝓝[Ioi 0] 0) (𝓝 (0 : ℂ)) := by
    have hh := ((tendsto_const_nhds.mul he).mul hε :
      Tendsto (fun ε : ℝ => -(c : ℂ) * Complex.exp (-(ε : ℂ) * (U : ℂ)) * (ε : ℂ))
        (𝓝[Ioi 0] 0) (𝓝 (-(c : ℂ) * 1 * 0)))
    have hh0 : Tendsto (fun ε : ℝ => -(c : ℂ) *
        Complex.exp (-(ε : ℂ) * (U : ℂ)) * (ε : ℂ))
        (𝓝[Ioi 0] 0) (𝓝 (0 : ℂ)) := by simpa using hh
    apply hh0.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε0
    have hεp : 0 < ε := hε0
    have hn : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hεp.ne'
    rw [show K = laplace (density U (envelope σ c)) from rfl,
      envelope_first hU hσ hc (by simp only [add_re, ofReal_re]; linarith)]
    simp only [add_sub_cancel_left]
    field_simp
  have hK2c : Tendsto (fun ε : ℝ => (ε : ℂ) ^ 2 * deriv (deriv K) ((σ : ℂ) + (ε : ℂ)))
      (𝓝[Ioi 0] 0) (𝓝 (c : ℂ)) := by
    have hh : Tendsto (fun ε : ℝ => (c : ℂ) *
        Complex.exp (-(ε : ℂ) * (U : ℂ)) * (1 + (U : ℂ) * (ε : ℂ)))
        (𝓝[Ioi 0] 0) (𝓝 ((c : ℂ) * 1 * (1 + (U : ℂ) * 0))) :=
      (tendsto_const_nhds.mul he).mul (tendsto_const_nhds.add (tendsto_const_nhds.mul hε))
    have hh' : Tendsto (fun ε : ℝ => (c : ℂ) * Complex.exp (-(ε : ℂ) * (U : ℂ)) *
        (1 + (U : ℂ) * (ε : ℂ))) (𝓝[Ioi 0] 0) (𝓝 (c : ℂ)) := by
      simpa using hh
    apply hh'.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε0
    have hεp : 0 < ε := hε0
    have hn : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hεp.ne'
    rw [show K = laplace (density U (envelope σ c)) from rfl,
      envelope_second hU hσ hc (by simp only [add_re, ofReal_re]; linarith)]
    simp only [add_sub_cancel_left]
    field_simp
    ring
  have hm1 : Tendsto (fun ε : ℝ => (ε : ℂ) ^ 2 * moment μ 1 ((σ : ℂ) + (ε : ℂ)))
      (𝓝[Ioi 0] 0) (𝓝 (0 : ℂ)) := by
    have hh0 : Tendsto (fun ε : ℝ => -((ε : ℂ) ^ 2 * deriv K ((σ : ℂ) + (ε : ℂ))) +
        (ε : ℂ) ^ 2 * deriv S ((σ : ℂ) + (ε : ℂ)))
        (𝓝[Ioi 0] 0) (𝓝 (0 : ℂ)) := by simpa using hK1zero.neg.add hS1zero
    apply hh0.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε0
    rw [hG1 _ (by simp only [add_re, ofReal_re]; change 0 < ε at hε0; linarith)]
    ring
  have hm2 : Tendsto (fun ε : ℝ => (ε : ℂ) ^ 2 * moment μ 2 ((σ : ℂ) + (ε : ℂ)))
      (𝓝[Ioi 0] 0) (𝓝 (c : ℂ)) := by
    have hh0 : Tendsto (fun ε : ℝ => (ε : ℂ) ^ 2 * deriv (deriv K) ((σ : ℂ) + (ε : ℂ)) -
        (ε : ℂ) ^ 2 * deriv (deriv S) ((σ : ℂ) + (ε : ℂ)))
        (𝓝[Ioi 0] 0) (𝓝 (c : ℂ)) := by simpa using hK2c.sub hS2zero
    apply hh0.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε0
    rw [hG2 _ (by simp only [add_re, ofReal_re]; change 0 < ε at hε0; linarith)]
    ring
  constructor
  · have hh := Complex.continuous_re.continuousAt.tendsto.comp hm1
    simpa only [← Complex.ofReal_add, real_moment, pow_one, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, ofReal_re, zero_re, Function.comp_def] using hh
  · have hh := Complex.continuous_re.continuousAt.tendsto.comp hm2
    simpa only [← Complex.ofReal_add, real_moment, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, ofReal_re, Function.comp_def] using hh

private theorem norm_pole_coefficient_le {μ : Measure ℝ} {σ c : ℝ} {a b : ℂ}
    (ha : a.re = σ) (hpos : ∀ᵐ u ∂μ, 0 ≤ u)
    (hi : ∀ x : ℝ, σ < x → Integrable (fun u : ℝ => Real.exp (-x * u)) μ)
    (hm1 : Tendsto (fun ε : ℝ => ε ^ 2 * ∫ u, u * Real.exp (-(σ + ε) * u) ∂μ)
      (𝓝[Ioi 0] 0) (𝓝 0))
    (hm2 : Tendsto (fun ε : ℝ => ε ^ 2 * ∫ u, u ^ 2 * Real.exp (-(σ + ε) * u) ∂μ)
      (𝓝[Ioi 0] 0) (𝓝 c))
    (hp : Tendsto (fun ε : ℝ => (ε : ℂ) ^ 2 * euler (laplace μ) (a + (ε : ℂ)))
      (𝓝[Ioi 0] 0) (𝓝 b)) : ‖b‖ ≤ ‖a‖ * c := by
  have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[Ioi 0] 0) (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun ε : ℝ => ‖a + (ε : ℂ)‖ *
      (ε ^ 2 * ∫ u, u ^ 2 * Real.exp (-(σ + ε) * u) ∂μ) +
      2 * (ε ^ 2 * ∫ u, u * Real.exp (-(σ + ε) * u) ∂μ))
      (𝓝[Ioi 0] 0) (𝓝 (‖a‖ * c)) := by
    simpa using (((tendsto_const_nhds.add hε).norm.mul hm2).add (hm1.const_mul 2))
  apply le_of_tendsto_of_tendsto hp.norm hr
  filter_upwards [self_mem_nhdsWithin] with ε hε0
  have hεp : 0 < ε := hε0
  have hz : σ < (a + (ε : ℂ)).re := by simp only [add_re, ofReal_re, ha]; linarith
  have h1 := moment_norm_le hpos 1 (a + (ε : ℂ))
  have h2 := moment_norm_le hpos 2 (a + (ε : ℂ))
  simp only [add_re, ofReal_re, ha, pow_one] at h1 h2
  rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hεp,
    euler, laplace_deriv hi hz, laplace_second hi hz]
  calc
    ε ^ 2 * ‖(a + (ε : ℂ)) * moment μ 2 (a + (ε : ℂ)) +
        2 * -moment μ 1 (a + (ε : ℂ))‖ ≤
        ε ^ 2 * (‖a + (ε : ℂ)‖ * ‖moment μ 2 (a + (ε : ℂ))‖ +
        2 * ‖moment μ 1 (a + (ε : ℂ))‖) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      simpa only [norm_mul, norm_neg, norm_ofNat] using
        norm_add_le ((a + (ε : ℂ)) * moment μ 2 (a + (ε : ℂ)))
          (2 * -moment μ 1 (a + (ε : ℂ)))
    _ ≤ ε ^ 2 * (‖a + (ε : ℂ)‖ * (∫ u, u ^ 2 * Real.exp (-(σ + ε) * u) ∂μ) +
        2 * (∫ u, u * Real.exp (-(σ + ε) * u) ∂μ)) := by
      gcongr
    _ = _ := by ring

/-- Every genuine zero in the open right half of the critical strip forces
arbitrarily late positive peaks with the full critical exponent and exact
multiplicity coefficient. -/
theorem critical_theta_tail_peak {ρ : ℂ} (hβ : (1 / 2 : ℝ) < ρ.re)
    (hβ1 : ρ.re < 1) (hzero : riemannZeta ρ = 0) :
    let m := analyticOrderNatAt riemannZeta ρ
    0 < m ∧ ρ.im ≠ 0 ∧
      ∀ c : ℝ, 0 ≤ c → c < (m : ℝ) / (‖ρ‖ * ‖ρ - 1‖) →
        ∀ T : ℝ, ∃ u : ℝ, max T (Real.log 2) < u ∧
          c < u * Real.exp ((1 - ρ.re) * u) * ActualThetaTailLaplace.f u := by
  dsimp only
  have hnonreal := zeta_zero_nonreal hβ hβ1 hzero
  have hmult := (ThetaLaplaceContinuation.theta_laplace_continuation 0 le_rfl).2.2.2.2.2.2.2
    ρ hβ hzero
  refine ⟨hmult.2.2.1, hnonreal, ?_⟩
  intro c hc hcA T
  by_contra! hn
  let σ := ρ.re - 1
  let a := ρ - 1
  let m := analyticOrderNatAt riemannZeta ρ
  let α : ℂ := -(m : ℂ) / ρ
  let U := max (max T (Real.log 2)) 1 + 1
  have hσ : σ < 0 := by dsimp [σ]; linarith
  have hσhalf : -(1 / 2 : ℝ) < σ := by dsimp [σ]; linarith
  have hU0 : 0 < U := by dsimp [U]; linarith [le_max_right (max T (Real.log 2)) (1 : ℝ)]
  have hU : ActualThetaTailLaplace.u₀ ≤ U := by
    dsimp [U, ActualThetaTailLaplace.u₀]
    linarith [le_max_left (max T (Real.log 2)) (1 : ℝ), le_max_right T (Real.log 2)]
  have hbound : ∀ u : ℝ, U < u → ActualThetaTailLaplace.f u ≤ envelope σ c u := by
    intro u hu
    have hu0 : 0 < u := hU0.trans hu
    have huT : max T (Real.log 2) < u := by
      dsimp [U] at hu
      linarith [le_max_left (max T (Real.log 2)) (1 : ℝ)]
    have hh := hn u huT
    have hep : 0 < u * Real.exp ((1 - ρ.re) * u) := mul_pos hu0 (Real.exp_pos _)
    calc
      ActualThetaTailLaplace.f u ≤ c / (u * Real.exp ((1 - ρ.re) * u)) := by
        apply (le_div_iff₀ hep).mpr
        nlinarith [hh]
      _ = envelope σ c u := by
        dsimp [envelope, σ]
        rw [show (ρ.re - 1) * u = -((1 - ρ.re) * u) by ring, Real.exp_neg]
        field_simp
  let μ := density U (gap σ c)
  let K := laplace (density U (envelope σ c))
  let G := laplace μ
  obtain ⟨hi, hfi, hL, hODE⟩ := comparison_halfplane hU hU0 hσ hσhalf hc hbound
  have hK := envelope_analytic hU0 hσ hc
  have heq : ∀ z : ℂ, σ < z.re → G z = K z - ActualThetaTailLaplace.L U z := by
    intro z hz
    exact gap_laplace_eq hU hU0 hσ hc hbound hz (hfi _ hz)
  have hGeuler : ∀ z : ℂ, σ < z.re → AnalyticAt ℂ (forcing U) z →
      euler G z = envelopeEuler U σ c z - forcing U z := by
    intro z hz hR
    have he : G =ᶠ[𝓝 z] fun w => K w - ActualThetaTailLaplace.L U w := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
        with w hw using heq w hw
    rw [euler_congr he, euler_sub (hK z hz) (hL z hz),
      envelope_euler hU0 hσ hc hz, hODE z hz hR]
  have hRσ := forcing_real_analytic U hU0.le hσhalf
  obtain ⟨r, hr, hrr⟩ := Metric.mem_nhds_iff.mp hRσ.eventually_analyticAt
  have hRball : DifferentiableOn ℂ (forcing U) (Metric.ball (σ : ℂ) r) :=
    fun z hz => (hrr hz).differentiableAt.differentiableWithinAt
  have hFhalf : DifferentiableOn ℂ (ActualThetaTailLaplace.L U)
      (D5.S3.Analytic.Laplace.EulerLocalContinuation.rightHalfDisk σ r) :=
    hL.differentiableOn.mono (fun _ hz => hz.2)
  obtain ⟨δ, hδ, _, H, hH, hHS⟩ :=
    D5.S3.Analytic.Laplace.EulerLocalContinuation.exists_extension_of_ne_zero hσ.ne hr
      hRball hFhalf (fun z hz => hODE z hz.2 (hrr hz.1))
  obtain ⟨hm1, hm2⟩ := boundary_moment_limits hU0 hσ hc hδ hi hL heq hH hHS
  obtain ⟨_, ha0, _, _, _, J, hJ, _, hLaurent, _, _⟩ :=
    (ThetaLaplaceContinuation.theta_laplace_continuation U hU0.le).2.2.2.2.2.2.2 ρ hβ hzero
  have hare : a.re = σ := by simp [a, σ]
  have hPa : AnalyticAt ℂ (envelopeEuler U σ c) a := by
    apply envelopeEuler_analytic
    intro he
    have hh := congrArg Complex.im he
    simp only [a, sub_im, one_im, sub_zero, ofReal_im] at hh
    exact hnonreal hh
  let W : ℂ → ℂ := fun z => envelopeEuler U σ c z - (J z - deriv J z + boundary U z)
  have hW : AnalyticAt ℂ W a := hPa.sub ((hJ.sub hJ.deriv).add (by unfold boundary; fun_prop))
  have hlocal : ∀ᶠ z : ℂ in 𝓝 a,
      z ≠ a → (fun z => -deriv (ThetaLaplaceContinuation.M U) z + ThetaLaplaceContinuation.M U z)
        =ᶠ[𝓝 z] (fun z => α / (z - a) ^ 2 + α / (z - a) + J z - deriv J z) := by
    have hh := eventually_nhds_nhdsWithin.mpr hLaurent
    filter_upwards [hh] with z hz hza
    exact hz.filter_mono (nhdsWithin_eq_nhds.mpr
      (isClosed_singleton.isOpen_compl.mem_nhds hza) |>.ge)
  have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[Ioi 0] 0) (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hp : Tendsto (fun ε : ℝ => a + (ε : ℂ)) (𝓝[Ioi 0] 0) (𝓝 a) := by
    simpa using tendsto_const_nhds.add hε
  have hpNE : Tendsto (fun ε : ℝ => a + (ε : ℂ)) (𝓝[Ioi 0] 0) (𝓝[≠] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hp, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε0
    have hεp : 0 < ε := hε0
    simpa using Complex.ofReal_ne_zero.mpr hεp.ne'
  have hlim : Tendsto (fun ε : ℝ => (ε : ℂ) ^ 2 * euler G (a + (ε : ℂ)))
      (𝓝[Ioi 0] 0) (𝓝 (-α)) := by
    have hh : Tendsto (fun ε : ℝ => -α - α * (ε : ℂ) +
        (ε : ℂ) ^ 2 * W (a + (ε : ℂ))) (𝓝[Ioi 0] 0) (𝓝 (-α)) := by
      simpa using (tendsto_const_nhds.sub (tendsto_const_nhds.mul hε)).add
        ((hε.pow 2).mul (hW.continuousAt.tendsto.comp hp))
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin, hp.eventually hlocal,
      hp.eventually hJ.eventually_analyticAt, hpNE.eventually hLaurent]
      with ε hε0 hl hJz hTz
    have hεp : 0 < ε := hε0
    have hn : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hεp.ne'
    have hza : a + (ε : ℂ) ≠ a := by simpa using hn
    have hd : a + (ε : ℂ) - a ≠ 0 := sub_ne_zero.mpr hza
    have hTa : AnalyticAt ℂ
        (fun z => -deriv (ThetaLaplaceContinuation.M U) z + ThetaLaplaceContinuation.M U z)
        (a + (ε : ℂ)) := by
      apply (((((analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow 2)
          (pow_ne_zero 2 hd)).add (analyticAt_const.div
          (analyticAt_id.sub analyticAt_const) hd)).add hJz).sub hJz.deriv)).congr
      exact (hl hza).symm
    have hR : AnalyticAt ℂ (forcing U) (a + (ε : ℂ)) :=
      hTa.add (by unfold boundary; fun_prop)
    rw [hGeuler _ (by simp only [add_re, ofReal_re, hare]; linarith) hR]
    change _ = (ε : ℂ) ^ 2 *
      (envelopeEuler U σ c (a + (ε : ℂ)) -
        ((-deriv (ThetaLaplaceContinuation.M U) (a + (ε : ℂ)) +
          ThetaLaplaceContinuation.M U (a + (ε : ℂ))) + boundary U (a + (ε : ℂ))))
    change -deriv (ThetaLaplaceContinuation.M U) (a + (ε : ℂ)) +
        ThetaLaplaceContinuation.M U (a + (ε : ℂ)) =
        α / (a + (ε : ℂ) - a) ^ 2 + α / (a + (ε : ℂ) - a) +
          J (a + (ε : ℂ)) - deriv J (a + (ε : ℂ)) at hTz
    rw [hTz]
    dsimp only [W]
    simp only [add_sub_cancel_left]
    field_simp
    ring
  have hnorm := norm_pole_coefficient_le hare (density_nonneg hU0.le (gap σ c)) hi hm1 hm2 hlim
  have hρ0 : ρ ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
  have hρnorm : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  have hanorm : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hcoef : (m : ℝ) / ‖ρ‖ ≤ ‖a‖ * c := by
    simpa only [α, norm_neg, norm_div, Complex.norm_natCast] using hnorm
  have hA : (m : ℝ) / (‖ρ‖ * ‖a‖) ≤ c := by
    apply (div_le_iff₀ (mul_pos hρnorm hanorm)).mpr
    have hh := (div_le_iff₀ hρnorm).mp hcoef
    nlinarith
  exact (not_le_of_gt hcA) hA

#print axioms critical_theta_tail_peak

end D5.S3.Weil.Mertens.CriticalThetaTailPeak

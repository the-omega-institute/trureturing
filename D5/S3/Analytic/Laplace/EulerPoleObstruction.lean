/- GID: D5/S3/Analytic/Laplace/EulerPoleObstruction
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/EulerPoleObstruction
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: Signed Euler double-pole obstruction for actual integrable Laplace tails. -/

import D5.S3.Analytic.Laplace.PositiveEulerContinuation
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual integrable tails and signed Euler pole obstruction. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology

namespace D5.S3.Analytic.Laplace.EulerPoleObstruction

def kernel (g : ℝ → ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-z * (u : ℂ)) * (g u : ℂ)

/-- The finite head has the same orientation as the removed part of an Ioi tail. -/
def finiteHead (g : ℝ → ℝ) (U V : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Ioc U V, kernel g z u

private theorem kernel_aestronglyMeasurable {g : ℝ → ℝ} {μ : Measure ℝ}
    (hg : AEStronglyMeasurable g μ) (z : ℂ) :
    AEStronglyMeasurable (kernel g z) μ :=
  (by fun_prop : Continuous (fun u : ℝ => Complex.exp (-z * (u : ℂ)))).aestronglyMeasurable.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hg)

private theorem kernel_norm (g : ℝ → ℝ) (z : ℂ) (u : ℝ) :
    ‖kernel g z u‖ = Real.exp (-z.re * u) * ‖g u‖ := by
  simp [kernel, Complex.norm_exp, Complex.mul_re]

private theorem kernel_hasDeriv (g : ℝ → ℝ) (u : ℝ) (z : ℂ) :
    HasDerivAt (fun w => kernel g w u) (-(u : ℂ) * kernel g z u) z := by
  have h := (((hasDerivAt_id z).neg).mul_const (u : ℂ)).cexp.mul_const (g u : ℂ)
  convert h using 1 <;> dsimp [kernel] <;> ring

/-- An arbitrary L1 source times a continuous exponential is integrable on the head. -/
private theorem kernel_integrable_Ioc {g : ℝ → ℝ} {U V : ℝ}
    (hg : IntegrableOn g (Ioc U V)) (z : ℂ) :
    IntegrableOn (kernel g z) (Ioc U V) := by
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc U V)).exists_bound_of_continuousOn
    (f := fun u : ℝ => Complex.exp (-z * (u : ℂ))) (by fun_prop)
  refine (hg.norm.const_mul K).mono'
    (kernel_aestronglyMeasurable hg.aestronglyMeasurable z) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  change ‖Complex.exp (-z * (u : ℂ)) * (g u : ℂ)‖ ≤ K * ‖g u‖
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (hK u ⟨hu.1.le, hu.2⟩) (norm_nonneg _)

/-- Local domination is K * norm g; no essential or pointwise bound on g is used. -/
theorem finiteHead_entire {g : ℝ → ℝ} {U V : ℝ}
    (hg : IntegrableOn g (Ioc U V)) : Differentiable ℂ (finiteHead g U V) := by
  intro z
  obtain ⟨K, hK⟩ := ((isCompact_closedBall z (1 : ℝ)).prod
    (isCompact_Icc : IsCompact (Icc U V))).exists_bound_of_continuousOn
      (f := fun p : ℂ × ℝ => -(p.2 : ℂ) * Complex.exp (-p.1 * (p.2 : ℂ)))
      (by fun_prop)
  have hm (w : ℂ) : AEStronglyMeasurable
      (fun u : ℝ => -(u : ℂ) * kernel g w u) (volume.restrict (Ioc U V)) :=
    (by fun_prop : Continuous (fun u : ℝ => -(u : ℂ))).aestronglyMeasurable.mul
      (kernel_aestronglyMeasurable hg.aestronglyMeasurable w)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := kernel g) (F' := fun w u => -(u : ℂ) * kernel g w u)
    (μ := volume.restrict (Ioc U V)) (s := Metric.ball z 1)
    (bound := fun u : ℝ => K * ‖g u‖)
    (Metric.ball_mem_nhds z zero_lt_one)
    (Eventually.of_forall fun w => kernel_aestronglyMeasurable hg.aestronglyMeasurable w)
    (kernel_integrable_Ioc hg z) (hm z) ?_ (hg.norm.const_mul K)
    (Eventually.of_forall fun u w _ => kernel_hasDeriv g u w)
  · exact h.2.differentiableAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    intro w hw
    rw [kernel, ← mul_assoc, norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right
      (hK (w, u) ⟨Metric.ball_subset_closedBall hw, hu.1.le, hu.2⟩) (norm_nonneg _)

private theorem kernel_integrable_Ioi {g : ℝ → ℝ} {U : ℝ}
    (hg : IntegrableOn g (Ioi U)) (hU : 0 ≤ U) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (kernel g z) (Ioi U) := by
  refine hg.norm.mono' (kernel_aestronglyMeasurable hg.aestronglyMeasurable z) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [kernel_norm]
  have he : Real.exp (-z.re * u) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz.le) (hU.trans hu.le))
  exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq (one_mul _)

private theorem first_exp_bound {b : ℝ} (hb : 0 < b) (u : ℝ) :
    u * Real.exp (-b * u) ≤ Real.exp (-1) / b := by
  apply (le_div_iff₀ hb).mpr
  calc
    (u * Real.exp (-b * u)) * b = (b * u) * Real.exp (-(b * u)) := by
      simp only [neg_mul]
      ring
    _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one (b * u)

/-- Actual L1-tail analyticity is asserted only in the positive half-plane. -/
theorem tail_analytic {g : ℝ → ℝ} {U : ℝ}
    (hg : IntegrableOn g (Ioi U)) (hU : 0 ≤ U) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∫ u in Ioi U, kernel g z u) {z | 0 < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro z hz
  change 0 < z.re at hz
  have hb : 0 < z.re / 2 := by linarith
  have hm (w : ℂ) : AEStronglyMeasurable
      (fun u : ℝ => -(u : ℂ) * kernel g w u) (volume.restrict (Ioi U)) :=
    (by fun_prop : Continuous (fun u : ℝ => -(u : ℂ))).aestronglyMeasurable.mul
      (kernel_aestronglyMeasurable hg.aestronglyMeasurable w)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := kernel g) (F' := fun w u => -(u : ℂ) * kernel g w u)
    (μ := volume.restrict (Ioi U)) (s := {w : ℂ | z.re / 2 < w.re})
    (bound := fun u : ℝ => Real.exp (-1) / (z.re / 2) * ‖g u‖)
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp; linarith))
    (Eventually.of_forall fun w => kernel_aestronglyMeasurable hg.aestronglyMeasurable w)
    (kernel_integrable_Ioi hg hU hz) (hm z) ?_ (hg.norm.const_mul _)
    (Eventually.of_forall fun u w _ => kernel_hasDeriv g u w)
  · exact h.2.differentiableAt.differentiableWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    have hu0 : 0 ≤ u := hU.trans hu.le
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hu0, kernel_norm]
    calc
      u * (Real.exp (-w.re * u) * ‖g u‖) =
          (u * Real.exp (-w.re * u)) * ‖g u‖ := by ring
      _ ≤ (u * Real.exp (-(z.re / 2) * u)) * ‖g u‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hu0
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (neg_le_neg hw.le) hu0)
      _ ≤ Real.exp (-1) / (z.re / 2) * ‖g u‖ :=
        mul_le_mul_of_nonneg_right (first_exp_bound hb u) (norm_nonneg _)

/-- Exact Ioc/Ioi partition; the correction is subtracted from the later tail. -/
theorem tail_cutoff {g : ℝ → ℝ} {U V : ℝ}
    (hg : IntegrableOn g (Ioi U)) (hU : 0 ≤ U) (hUV : U ≤ V)
    {z : ℂ} (hz : 0 < z.re) :
    (∫ u in Ioi V, kernel g z u) =
      (∫ u in Ioi U, kernel g z u) - finiteHead g U V z := by
  have hi := kernel_integrable_Ioi hg hU hz
  have he := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi hUV))
  rw [Ioc_union_Ioi_eq_Ioi hUV] at he
  change (∫ u in Ioi U, kernel g z u) =
    finiteHead g U V z + (∫ u in Ioi V, kernel g z u) at he
  linear_combination -he

end D5.S3.Analytic.Laplace.EulerPoleObstruction

namespace D5.S3.Analytic.Laplace.EulerPoleObstruction

/-- The actual cutoff integral, including its totalized values outside convergence. -/
def tailLaplace (g : ℝ → ℝ) (U : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Ioi U, Complex.exp (-z * (u : ℂ)) * (g u : ℂ)

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

def envelope (σ c : ℝ) (u : ℝ) : ℝ := c * Real.exp (σ * u) / u

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

def euler (F : ℂ → ℂ) (z : ℂ) : ℂ := z * deriv (deriv F) z + 2 * deriv F z

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

/-- Analytic differentiation preserves regularity of the Euler expression. -/
private theorem euler_analyticAt {F : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z) :
    AnalyticAt ℂ (euler F) z :=
  (analyticAt_id.mul hF.deriv.deriv).add (analyticAt_const.mul hF.deriv)

private theorem euler_const_mul (k : ℂ) (F : ℂ → ℂ) (z : ℂ) :
    euler (fun w => k * F w) z = k * euler F z := by
  simp only [euler, deriv_const_mul_field']
  ring

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

private def gap (g : ℝ → ℝ) (s σ c : ℝ) (u : ℝ) : ℝ := envelope σ c u - s * g u

private theorem gap_integrable {g : ℝ → ℝ} {U s σ c : ℝ} (hU : IntegrableOn g (Ioi U))
    (hU0 : 0 < U) (hσ : σ < 0) (hc : 0 ≤ c) : IntegrableOn (gap g s σ c) (Ioi U) :=
  (envelope_integrable hU0 hσ hc).sub (hU.const_mul s)

private theorem gap_nonneg {g : ℝ → ℝ} {U s σ c : ℝ}
    (hbound : ∀ u : ℝ, U < u → s * g u ≤ envelope σ c u) :
    ∀ᵐ u ∂volume.restrict (Ioi U), 0 ≤ gap g s σ c u := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact sub_nonneg.mpr (hbound u hu)

private theorem gap_laplace_eq {g : ℝ → ℝ} {U s σ c : ℝ} (hU : IntegrableOn g (Ioi U))
    (hU0 : 0 < U) (hσ : σ < 0) (hc : 0 ≤ c)
    (hbound : ∀ u : ℝ, U < u → s * g u ≤ envelope σ c u)
    {z : ℂ} (hz : σ < z.re)
    (hfi : IntegrableOn (fun u => (s * g u) *
      Real.exp (-z.re * u)) (Ioi U)) :
    laplace (density U (gap g s σ c)) z =
      laplace (density U (envelope σ c)) z - (s : ℂ) * tailLaplace g U z := by
  rw [density_laplace (gap_integrable hU hU0 hσ hc) (gap_nonneg hbound),
    density_laplace (envelope_integrable hU0 hσ hc) (envelope_nonneg hU0 hc),
    tailLaplace]
  simp only [gap, Complex.ofReal_sub, mul_sub]
  rw [integral_sub
    (complex_weight_integrable (envelope_integrable hU0 hσ hc).aestronglyMeasurable
      (envelope_weighted_integrable hU0 hc hz))
    (complex_weight_integrable (hU.const_mul s).aestronglyMeasurable hfi)]
  have he : (fun u : ℝ => Complex.exp (-z * (u : ℂ)) *
      ((s * g u : ℝ) : ℂ)) =
      (fun u : ℝ => (s : ℂ) *
        (Complex.exp (-z * (u : ℂ)) * (g u : ℂ))) := by
    funext u
    push_cast
    ring
  rw [he, integral_const_mul]

private theorem comparison_halfplane {g : ℝ → ℝ} {U s σ c : ℝ}
    (hU : IntegrableOn g (Ioi U)) (hU0 : 0 < U)
    (hσ : σ < 0) {d : ℝ} (hdσ : d < σ) (hc : 0 ≤ c)
    {Φ : ℂ → ℂ} (hΦm : MeromorphicOn Φ {z | d < z.re})
    (hΦr : ∀ x : ℝ, σ ≤ x → x ≤ 0 → AnalyticAt ℂ Φ (x : ℂ))
    (hode : ∀ z : ℂ, 0 < z.re → euler (tailLaplace g U) z = Φ z)
    (hbound : ∀ u : ℝ, U < u → s * g u ≤ envelope σ c u) :
    (∀ x : ℝ, σ < x → Integrable (fun u => Real.exp (-x * u)) (density U (gap g s σ c))) ∧
    (∀ x : ℝ, σ < x → IntegrableOn
      (fun u => (s * g u) * Real.exp (-x * u)) (Ioi U)) ∧
    AnalyticOnNhd ℂ (fun z => (s : ℂ) * tailLaplace g U z) {z | σ < z.re} ∧
    (∀ z : ℂ, σ < z.re → AnalyticAt ℂ Φ z →
      euler (fun w => (s : ℂ) * tailLaplace g U w) z =
        (s : ℂ) * Φ z) := by
  let μ := density U (gap g s σ c)
  let K := laplace (density U (envelope σ c))
  let G := laplace μ
  let S : ℂ → ℂ := fun z => (s : ℂ) * tailLaplace g U z
  have hgi := gap_integrable (s := s) hU hU0 hσ hc
  have hgp := gap_nonneg hbound
  haveI : IsFiniteMeasure μ := density_finite hgi hgp
  have hpos := density_nonneg hU0.le (gap g s σ c)
  have hK := envelope_analytic hU0 hσ hc
  have hfi0 : ∀ x : ℝ, 0 < x → IntegrableOn
      (fun u => (s * g u) * Real.exp (-x * u)) (Ioi U) := by
    intro x hx
    apply (hU.const_mul s).norm.mono'
    · exact (hU.const_mul s).aestronglyMeasurable.mul (by fun_prop)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
      apply mul_le_of_le_one_right (abs_nonneg _)
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx.le)
        (hU0.le.trans hu.le))
  have hGbase : AnalyticOnNhd ℂ G {z | 0 < z.re} := by
    apply D5.S3.Analytic.Laplace.PositiveEulerContinuation.analytic_laplace
    intro x hx
    apply (integrable_const (1 : ℝ)).mono'
    · fun_prop
    · filter_upwards [hpos] with u hu
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx.le) hu)
  have hSbase : AnalyticOnNhd ℂ S {z | 0 < z.re} := by
    intro z hz
    apply ((hK z (lt_trans hσ hz)).sub (hGbase z hz)).congr
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
      with w hw
    have he := gap_laplace_eq hU hU0 hσ hc hbound (lt_trans hσ hw) (hfi0 _ hw)
    change G w = K w - S w at he
    change K w - G w = S w
    linear_combination -he
  have hG0 : ∀ z : ℂ, 0 < z.re → euler G z =
      envelopeEuler U σ c z - (s : ℂ) * Φ z := by
    intro z hz
    have he : G =ᶠ[𝓝 z] fun w => K w - S w := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
        with w hw
      exact gap_laplace_eq hU hU0 hσ hc hbound (lt_trans hσ hw) (hfi0 _ hw)
    have hS0 : AnalyticAt ℂ S z := hSbase z hz
    rw [euler_congr he, euler_sub (hK z (lt_trans hσ hz))
      hS0,
      envelope_euler hU0 hσ hc (lt_trans hσ hz)]
    change _ - euler (fun w => (s : ℂ) * tailLaplace g U w) z = _
    rw [euler_const_mul, hode z hz]
  have hP : AnalyticOnNhd ℂ (envelopeEuler U σ c) {z | σ < z.re} := by
    intro z hz
    apply envelopeEuler_analytic
    intro he
    change σ < z.re at hz
    exact (lt_irrefl σ) (by simpa only [he, ofReal_re] using hz)
  have hRm : MeromorphicOn (fun z => envelopeEuler U σ c z - (s : ℂ) * Φ z)
      {z | σ < z.re} := hP.meromorphicOn.sub
    (analyticOnNhd_const.meromorphicOn.mul
      (fun z hz => hΦm z (lt_trans hdσ hz)))
  have hRa : ∀ x : ℝ, σ < x → x ≤ 0 →
      AnalyticAt ℂ (fun z => envelopeEuler U σ c z - (s : ℂ) * Φ z) (x : ℂ) := by
    intro x hx hx0
    exact (hP x hx).sub
      (analyticAt_const.mul (hΦr x hx.le hx0))
  obtain ⟨hi, hG⟩ := D5.S3.Analytic.Laplace.PositiveEulerContinuation.integrable_and_analytic_of_euler_corridor
    (μ := μ) (X := id) (by fun_prop) hpos hσ hRm hRa hG0
  have hfi : ∀ x : ℝ, σ < x → IntegrableOn
      (fun u => (s * g u) * Real.exp (-x * u)) (Ioi U) := by
    intro x hx
    have hgx := (density_integrable hgi hgp _).mp (hi x hx)
    convert (envelope_weighted_integrable hU0 hc hx).sub hgx using 1
    ext u
    dsimp only [gap, Pi.sub_apply, id_eq]
    ring
  have heq : ∀ z : ℂ, σ < z.re → S z = K z - G z := by
    intro z hz
    have he := gap_laplace_eq hU hU0 hσ hc hbound hz (hfi z.re hz)
    change G z = K z - S z at he
    linear_combination he
  have hS : AnalyticOnNhd ℂ S {z | σ < z.re} := by
    intro z hz
    apply ((hK z hz).sub (hG z hz)).congr
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
      with w hw using (heq w hw).symm
  refine ⟨hi, hfi, hS, ?_⟩
  let D : ℂ → ℂ := fun z => euler S z - (s : ℂ) * Φ z
  have hDm : MeromorphicOn D {z | σ < z.re} := by
    have hm := hS.meromorphicOn
    exact ((analyticOnNhd_id.meromorphicOn.mul hm.deriv.deriv).add
      (analyticOnNhd_const.meromorphicOn.mul hm.deriv)).sub
      (analyticOnNhd_const.meromorphicOn.mul
        (fun z hz => hΦm z (lt_trans hdσ hz)))
  have hD1 : meromorphicOrderAt D (1 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with z hz
    apply sub_eq_zero.mpr
    change euler (fun w => (s : ℂ) * tailLaplace g U w) z = _
    rw [euler_const_mul, hode z hz]
  intro z hz hRz
  have htop := hDm.meromorphicOrderAt_eq_top_of_isPreconnected
    (convex_halfSpace_re_gt σ).isPreconnected
    (show σ < (1 : ℂ).re by simp only [one_re]; linarith) hz hD1
  have hDc : ContinuousAt D z := by
    exact ((continuousAt_id.mul (hS z hz).deriv.deriv.continuousAt).add
      ((hS z hz).deriv.continuousAt.const_mul 2)).sub (hRz.continuousAt.const_mul (s : ℂ))
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

/-- Nonzero full normalized coefficient; combined with meromorphicity this is
an actual double pole, with no arbitrary assignment at the pole constrained. -/
structure DoublePole (Φ : ℂ → ℂ) (a Λ : ℂ) : Prop where
  coefficient_ne_zero : Λ ≠ 0
  normalized_limit : Tendsto (fun z : ℂ => (z - a) ^ 2 * Φ z) (𝓝[≠] a) (𝓝 Λ)

/-- An analytic subtraction preserves the full complex punctured coefficient,
including its nonzero value; this is not merely a limit along a real ray. -/
private theorem DoublePole.sub_analytic {Φ H : ℂ → ℂ} {a Λ : ℂ}
    (hpole : DoublePole Φ a Λ) (hH : AnalyticAt ℂ H a) :
    DoublePole (fun z => Φ z - H z) a Λ := by
  refine ⟨hpole.coefficient_ne_zero, ?_⟩
  have hz : Tendsto (fun z : ℂ => z - a) (𝓝[≠] a) (𝓝 (0 : ℂ)) := by
    simpa using ((tendsto_id : Tendsto (id : ℂ → ℂ) (𝓝 a) (𝓝 a)).sub_const a).mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun z : ℂ => (z - a) ^ 2 * H z)
      (𝓝[≠] a) (𝓝 (0 : ℂ)) := by
    simpa using (hz.pow 2).mul (hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [mul_sub, sub_zero] using hpole.normalized_limit.sub hzero

/-- A signed pointwise envelope bounds the entire complex double-pole coefficient.
The gap has an actual finite positive density. Its zero-cut continuation is the
L1 boundary-limit branch of `integrable_and_analytic_of_euler_corridor`.
Neither convergence to the left of zero nor a moment bound is an input. -/
theorem coefficient_le_of_pointwise_envelope {g : ℝ → ℝ} {U d σ c s : ℝ} {Φ : ℂ → ℂ}
    (hg : IntegrableOn g (Ioi U)) (hU : 0 < U) (hdσ : d < σ) (hσ : σ < 0)
    (hΦm : MeromorphicOn Φ {z | d < z.re})
    (hΦr : ∀ x : ℝ, σ ≤ x → x ≤ 0 → AnalyticAt ℂ Φ (x : ℂ))
    (hode : ∀ z : ℂ, 0 < z.re → euler (tailLaplace g U) z = Φ z)
    {a Λ : ℂ} (ha : a.re = σ) (him : a.im ≠ 0) (hpole : DoublePole Φ a Λ)
    (hs : s ^ 2 = 1) (hc : 0 ≤ c)
    (hbound : ∀ u : ℝ, U < u → s * g u ≤ envelope σ c u) :
    ‖Λ‖ ≤ ‖a‖ * c := by
  let μ := density U (gap g s σ c)
  let K := laplace (density U (envelope σ c))
  let G := laplace μ
  let S : ℂ → ℂ := fun z => (s : ℂ) * tailLaplace g U z
  obtain ⟨hi, hfi, hS, hODE⟩ := comparison_halfplane hg hU hσ hdσ hc hΦm hΦr hode hbound
  have hK := envelope_analytic hU hσ hc
  have heq : ∀ z : ℂ, σ < z.re → G z = K z - S z := by
    intro z hz
    exact gap_laplace_eq hg hU hσ hc hbound hz (hfi _ hz)
  have hGeuler : ∀ z : ℂ, σ < z.re → AnalyticAt ℂ Φ z →
      euler G z = envelopeEuler U σ c z - (s : ℂ) * Φ z := by
    intro z hz hR
    have he : G =ᶠ[𝓝 z] fun w => K w - S w := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
        with w hw using heq w hw
    rw [euler_congr he, euler_sub (hK z hz) (hS z hz),
      envelope_euler hU hσ hc hz, hODE z hz hR]
  obtain ⟨r, hr, hrr⟩ := Metric.mem_nhds_iff.mp
    (hΦr σ le_rfl hσ.le).eventually_analyticAt
  have hRball : DifferentiableOn ℂ (fun z => (s : ℂ) * Φ z) (Metric.ball (σ : ℂ) r) :=
    fun z hz => (analyticAt_const.mul (hrr hz)).differentiableAt.differentiableWithinAt
  have hFhalf : DifferentiableOn ℂ S
      (D5.S3.Analytic.Laplace.EulerLocalContinuation.rightHalfDisk σ r) :=
    hS.differentiableOn.mono (fun _ hz => hz.2)
  obtain ⟨δ, hδ, _, H, hH, hHS⟩ :=
    D5.S3.Analytic.Laplace.EulerLocalContinuation.exists_extension_of_ne_zero hσ.ne hr
      hRball hFhalf (fun z hz => hODE z hz.2 (hrr hz.1))
  obtain ⟨hm1, hm2⟩ := boundary_moment_limits hU hσ hc hδ hi hS heq hH hHS
  have hPa : AnalyticAt ℂ (envelopeEuler U σ c) a := by
    apply envelopeEuler_analytic
    intro he
    apply him
    have hh := congrArg Complex.im he
    simpa only [ofReal_im] using hh
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
  have hΦlim : Tendsto (fun ε : ℝ => (ε : ℂ) ^ 2 * Φ (a + (ε : ℂ)))
      (𝓝[Ioi 0] 0) (𝓝 Λ) := by
    simpa only [Function.comp_def, add_sub_cancel_left] using hpole.normalized_limit.comp hpNE
  have hPlim : Tendsto (fun ε : ℝ => (ε : ℂ) ^ 2 * envelopeEuler U σ c (a + (ε : ℂ)))
      (𝓝[Ioi 0] 0) (𝓝 (0 : ℂ)) := by
    simpa using (hε.pow 2).mul (hPa.continuousAt.tendsto.comp hp)
  have hlim : Tendsto (fun ε : ℝ => (ε : ℂ) ^ 2 * euler G (a + (ε : ℂ)))
      (𝓝[Ioi 0] 0) (𝓝 (-(s : ℂ) * Λ)) := by
    have hh : Tendsto (fun ε : ℝ =>
        (ε : ℂ) ^ 2 * envelopeEuler U σ c (a + (ε : ℂ)) -
          (s : ℂ) * ((ε : ℂ) ^ 2 * Φ (a + (ε : ℂ))))
        (𝓝[Ioi 0] 0) (𝓝 (-(s : ℂ) * Λ)) := by
      simpa using hPlim.sub (tendsto_const_nhds.mul hΦlim)
    have hmer : MeromorphicAt Φ a := hΦm a (by change d < a.re; rw [ha]; exact hdσ)
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin, hpNE.eventually hmer.eventually_analyticAt]
      with ε hε0 hR
    have hεp : 0 < ε := hε0
    rw [hGeuler _ (by simp only [add_re, ofReal_re, ha]; linarith) hR]
    ring
  have hnorm := norm_pole_coefficient_le ha (density_nonneg hU.le (gap g s σ c))
    hi hm1 hm2 hlim
  have hsabs : |s| = 1 := by nlinarith [sq_abs s, abs_nonneg s]
  have hsNorm : ‖(s : ℂ)‖ = 1 := by
    simpa only [norm_real, Real.norm_eq_abs] using hsabs
  simpa only [norm_mul, norm_neg, hsNorm, one_mul] using hnorm

/-- An eventual envelope at the fixed original cutoff suffices. Only the
finite Ioc head is removed; no bound or moments of g on that head are assumed.
The shifted forcing is Phi minus Euler(P), with the same full pole coefficient. -/
theorem coefficient_le_of_envelope {g : ℝ → ℝ} {U d σ c s : ℝ} {Φ : ℂ → ℂ}
    (hg : IntegrableOn g (Ioi U)) (hU : 0 < U) (hdσ : d < σ) (hσ : σ < 0)
    (hΦm : MeromorphicOn Φ {z | d < z.re})
    (hΦr : ∀ x : ℝ, σ ≤ x → x ≤ 0 → AnalyticAt ℂ Φ (x : ℂ))
    (hode : ∀ z : ℂ, 0 < z.re → euler (tailLaplace g U) z = Φ z)
    {a Λ : ℂ} (ha : a.re = σ) (him : a.im ≠ 0) (hpole : DoublePole Φ a Λ)
    (hs : s ^ 2 = 1) (hc : 0 ≤ c)
    (hbound : ∀ᶠ u : ℝ in atTop, s * g u ≤ envelope σ c u) :
    ‖Λ‖ ≤ ‖a‖ * c := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp hbound
  let V : ℝ := max U R + 1
  have hUV : U < V := by dsimp [V]; linarith [le_max_left U R]
  have hRV : R ≤ V := by dsimp [V]; linarith [le_max_right U R]
  have hgV : IntegrableOn g (Ioi V) := hg.mono_set (Ioi_subset_Ioi hUV.le)
  have hgHead : IntegrableOn g (Ioc U V) := hg.mono_set Ioc_subset_Ioi_self
  let P : ℂ → ℂ := finiteHead g U V
  have hP : Differentiable ℂ P := finiteHead_entire hgHead
  have hE : ∀ z : ℂ, AnalyticAt ℂ (euler P) z :=
    fun z => euler_analyticAt (hP.analyticAt z)
  let ΦV : ℂ → ℂ := fun z => Φ z - euler P z
  have hΦVm : MeromorphicOn ΦV {z | d < z.re} :=
    hΦm.sub (fun z _ => (hE z).meromorphicAt)
  have hΦVr : ∀ x : ℝ, σ ≤ x → x ≤ 0 → AnalyticAt ℂ ΦV (x : ℂ) :=
    fun x hx hx0 => (hΦr x hx hx0).sub (hE (x : ℂ))
  have hpoleV : DoublePole ΦV a Λ := hpole.sub_analytic (hE a)
  have hL : AnalyticOnNhd ℂ (tailLaplace g U) {z | 0 < z.re} := by
    intro z hz
    convert tail_analytic hg hU.le z hz using 1
    rfl
  have hcut : ∀ z : ℂ, 0 < z.re →
      tailLaplace g V z = tailLaplace g U z - P z := by
    intro z hz
    simpa only [tailLaplace, P, kernel] using
      tail_cutoff hg hU.le hUV.le hz
  have hodeV : ∀ z : ℂ, 0 < z.re → euler (tailLaplace g V) z = ΦV z := by
    intro z hz
    have he : tailLaplace g V =ᶠ[𝓝 z] fun w => tailLaplace g U w - P w := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
        with w hw using hcut w hw
    rw [euler_congr he, euler_sub (hL z hz) (hP.analyticAt z), hode z hz]
  exact coefficient_le_of_pointwise_envelope hgV (hU.trans hUV) hdσ hσ
    hΦVm hΦVr hodeV ha him hpoleV hs hc
    (fun u hu => hR u (hRV.trans hu.le))

/-- Both signs, every strict coefficient below the full norm ratio, and every
late cutoff follow from the forcing at one original cutoff. -/
theorem signed_peaks {g : ℝ → ℝ} {U₀ d σ : ℝ} {Φ : ℂ → ℂ}
    (hg : IntegrableOn g (Ioi U₀)) (hU₀ : 0 < U₀) (hdσ : d < σ) (hσ : σ < 0)
    (hΦm : MeromorphicOn Φ {z | d < z.re})
    (hreal : ∀ x : ℝ, σ ≤ x → x ≤ 0 → AnalyticAt ℂ Φ (x : ℂ))
    (hode : ∀ z : ℂ, 0 < z.re → euler (tailLaplace g U₀) z = Φ z)
    {a Λ : ℂ} (ha : a.re = σ) (him : a.im ≠ 0) (hpole : DoublePole Φ a Λ) :
    ∀ s : ℝ, s ^ 2 = 1 → ∀ c : ℝ, 0 ≤ c → c < ‖Λ‖ / ‖a‖ →
      ∀ T : ℝ, ∃ u : ℝ, max T U₀ < u ∧
        c < u * Real.exp (-σ * u) * (s * g u) := by
  intro s hs c hc hcA T
  by_contra! hn
  have hbound : ∀ᶠ u : ℝ in atTop, s * g u ≤ envelope σ c u := by
    filter_upwards [eventually_gt_atTop (max T U₀)] with u huT
    have hu0 : 0 < u := hU₀.trans
      (lt_of_le_of_lt (le_max_right T U₀) huT)
    have hh := hn u huT
    have hep : 0 < u * Real.exp (-σ * u) := mul_pos hu0 (Real.exp_pos _)
    calc
      s * g u ≤ c / (u * Real.exp (-σ * u)) := by
        apply (le_div_iff₀ hep).mpr
        nlinarith [hh]
      _ = envelope σ c u := by
        dsimp [envelope]
        rw [neg_mul, Real.exp_neg]
        field_simp
  have hcoef := coefficient_le_of_envelope
    hg hU₀ hdσ hσ hΦm hreal hode
    ha him hpole hs hc hbound
  have ha0 : a ≠ 0 := by intro he; apply him; simp [he]
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hA : ‖Λ‖ / ‖a‖ ≤ c := (div_le_iff₀ han).mpr (by nlinarith [hcoef])
  exact (not_le_of_gt hcA) hA

end D5.S3.Analytic.Laplace.EulerPoleObstruction

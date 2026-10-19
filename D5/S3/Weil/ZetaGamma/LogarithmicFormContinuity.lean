/- GID: D5/S3/Weil/ZetaGamma/LogarithmicFormContinuity
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/LogarithmicFormContinuity
   mirror-E: none(waiver:analytic-Gamma-form-continuity)
   anchors: []
   utility: none
   digest: Transport logarithmic Fourier-square error to the actual Gamma quadratic integral. -/

import D5.S3.Weil.ZetaExplicit.VerticalLine
import D5.S3.Weil.ZetaGamma.GammaFacts
import Mathlib.Algebra.Order.Field.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.LogarithmicFormContinuity

open MeasureTheory
open Filter
open scoped Topology

private def logWeight (t : ℝ) : ℝ := 1 + Real.log (1 + |t|)
private def angularFactor : ℝ := 1 / (2 * Real.pi)
private def gammaSymbol (t : ℝ) : ℝ := 2 * Real.pi * Zeta23.mu t
private def logEnergy (F : ℝ → ℂ) : ℝ :=
  angularFactor * ∫ t : ℝ, logWeight t * Complex.normSq (F t)
private def gammaQuadratic (F : ℝ → ℂ) : ℝ :=
  angularFactor * ∫ t : ℝ, gammaSymbol t * Complex.normSq (F t)
private def gammaMixed (F G : ℝ → ℂ) : ℂ :=
  (angularFactor : ℂ) * ∫ t : ℝ, (gammaSymbol t : ℂ) * star (F t) * G t

private theorem angularFactor_pos : 0 < angularFactor := by
  dsimp [angularFactor]
  positivity

private theorem logWeight_nonneg (t : ℝ) : 0 ≤ logWeight t := by
  have hlog : 0 ≤ Real.log (1 + |t|) :=
    Real.log_nonneg (by linarith [abs_nonneg t])
  dsimp [logWeight]
  linarith

private theorem logEnergy_nonneg (F : ℝ → ℂ) : 0 ≤ logEnergy F :=
  mul_nonneg angularFactor_pos.le
    (integral_nonneg fun t => mul_nonneg (logWeight_nonneg t) (Complex.normSq_nonneg _))

/-- The symbol is exactly the existing completed-zeta archimedean density;
there is no replacement scalar Gamma model in this statement. -/
private theorem actual_gamma_log_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      |2 * Real.pi * Zeta23.mu t| ≤
        C * (1 + Real.log (1 + |t|)) := by
  obtain ⟨A, hA, hpsi⟩ := Zeta23.WeilEF.digamma_growth_strip
  let C : ℝ := A * (1 + Real.log 2) + |Real.log Real.pi|
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro t
  let s : ℂ := (1 / 4 : ℂ) + Complex.I * (t : ℂ) / 2
  have hsre : s.re = (1 / 4 : ℝ) := by simp [s]
  have hsim : |s.im| = |t| / 2 := by simp [s, abs_div]
  have hpsi_t : ‖Complex.digamma s‖ ≤ A * Real.log (2 + |t| / 2) := by
    simpa only [hsim] using hpsi s (by norm_num [hsre]) (by norm_num [hsre])
  have hlog1 : 0 ≤ Real.log (1 + |t|) :=
    Real.log_nonneg (by linarith [abs_nonneg t])
  have hw : 1 ≤ 1 + Real.log (1 + |t|) := by linarith
  have hlog : Real.log (2 + |t| / 2) ≤
      (1 + Real.log 2) * (1 + Real.log (1 + |t|)) := by
    calc
      Real.log (2 + |t| / 2) ≤ Real.log (2 * (1 + |t|)) :=
        Real.log_le_log (by positivity) (by nlinarith [abs_nonneg t])
      _ = Real.log 2 + Real.log (1 + |t|) :=
        Real.log_mul (by norm_num) (by positivity)
      _ ≤ (1 + Real.log 2) * (1 + Real.log (1 + |t|)) := by
        nlinarith [mul_nonneg hlog2 hlog1]
  have hsymbol : 2 * Real.pi * Zeta23.mu t =
      (Complex.digamma s).re - Real.log Real.pi := by
    dsimp [Zeta23.mu, s]
    field_simp [Real.pi_ne_zero]
    <;> ring
  rw [hsymbol]
  calc
    |(Complex.digamma s).re - Real.log Real.pi| ≤
        |(Complex.digamma s).re| + |Real.log Real.pi| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (Complex.digamma s).re (-Real.log Real.pi)
    _ ≤ A * Real.log (2 + |t| / 2) + |Real.log Real.pi| := by
      exact add_le_add ((Complex.abs_re_le_norm _).trans hpsi_t) le_rfl
    _ ≤ A * ((1 + Real.log 2) * (1 + Real.log (1 + |t|))) +
        |Real.log Real.pi| * (1 + Real.log (1 + |t|)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hlog hA.le)
        (le_mul_of_one_le_right (abs_nonneg _) hw)
    _ = C * (1 + Real.log (1 + |t|)) := by dsimp [C]; ring

/-- First actual-symbol consumer: weighted Fourier square integrability
discharges the actual Gamma integrability obligation. -/
private theorem integrable_actual_gamma_normSq_of_log_weight
    {F : ℝ → ℂ} (hF : Continuous F)
    (hW : Integrable (fun t : ℝ =>
      (1 + Real.log (1 + |t|)) * Complex.normSq (F t))) :
    Integrable (fun t : ℝ =>
      (2 * Real.pi * Zeta23.mu t) * Complex.normSq (F t)) := by
  obtain ⟨C, _hC, hbound⟩ := actual_gamma_log_growth
  refine (hW.const_mul C).mono' ?_ (Filter.Eventually.of_forall ?_)
  · exact ((continuous_const.mul Zeta23.mu_smooth.continuous).mul
      (Complex.continuous_normSq.comp hF)).aestronglyMeasurable
  · intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
    calc
      |2 * Real.pi * Zeta23.mu t| * Complex.normSq (F t) ≤
          (C * (1 + Real.log (1 + |t|))) * Complex.normSq (F t) :=
        mul_le_mul_of_nonneg_right (hbound t) (Complex.normSq_nonneg _)
      _ = C * ((1 + Real.log (1 + |t|)) * Complex.normSq (F t)) := by ring

private theorem integrable_actual_gamma_mixed
    {C : ℝ} (hC : 0 ≤ C) (hgamma : ∀ t, |gammaSymbol t| ≤ C * logWeight t)
    {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G)
    (hWF : Integrable (fun t : ℝ => logWeight t * Complex.normSq (F t)))
    (hWG : Integrable (fun t : ℝ => logWeight t * Complex.normSq (G t))) :
    Integrable (fun t : ℝ => (gammaSymbol t : ℂ) * star (F t) * G t) := by
  have hcontinuous : Continuous gammaSymbol := continuous_const.mul Zeta23.mu_smooth.continuous
  refine ((hWF.add hWG).const_mul C).mono' ?_ (Eventually.of_forall ?_)
  · exact (((Complex.continuous_ofReal.comp hcontinuous).mul hF.star).mul
      hG).aestronglyMeasurable
  · intro t
    have hp : ‖F t‖ * ‖G t‖ ≤ Complex.normSq (F t) + Complex.normSq (G t) := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      nlinarith [two_mul_le_add_sq ‖F t‖ ‖G t‖, sq_nonneg ‖F t‖, sq_nonneg ‖G t‖]
    calc
      ‖(gammaSymbol t : ℂ) * star (F t) * G t‖ =
          |gammaSymbol t| * (‖F t‖ * ‖G t‖) := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_star]
        ring
      _ ≤ (C * logWeight t) * (Complex.normSq (F t) + Complex.normSq (G t)) :=
        mul_le_mul (hgamma t) hp (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (mul_nonneg hC (logWeight_nonneg t))
      _ = C * (logWeight t * Complex.normSq (F t) +
          logWeight t * Complex.normSq (G t)) := by ring

/-- The actual completed-zeta Gamma pairing, controlled by the actual
logarithmic energies. The scalar Young inequality is reused from Mathlib. -/
private theorem actual_gamma_mixed_young_bound
    {C : ℝ} (hC : 0 ≤ C) (hgamma : ∀ t, |gammaSymbol t| ≤ C * logWeight t)
    {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G)
    (hWF : Integrable (fun t : ℝ => logWeight t * Complex.normSq (F t)))
    (hWG : Integrable (fun t : ℝ => logWeight t * Complex.normSq (G t)))
    {delta : ℝ} (hdelta : 0 < delta) :
    ‖gammaMixed F G‖ ≤ (C / 2) * (delta * logEnergy F + delta⁻¹ * logEnergy G) := by
  have hmixed := integrable_actual_gamma_mixed hC hgamma hF hG hWF hWG
  have hmajor : Integrable (fun t : ℝ => (C / 2) *
      (delta * (logWeight t * Complex.normSq (F t)) +
       delta⁻¹ * (logWeight t * Complex.normSq (G t)))) :=
    ((hWF.const_mul delta).add (hWG.const_mul delta⁻¹)).const_mul (C / 2)
  have hint : (∫ t : ℝ, ‖(gammaSymbol t : ℂ) * star (F t) * G t‖) ≤
      ∫ t : ℝ, (C / 2) *
        (delta * (logWeight t * Complex.normSq (F t)) +
         delta⁻¹ * (logWeight t * Complex.normSq (G t))) := by
    apply integral_mono hmixed.norm hmajor
    intro t
    have hyoung : ‖F t‖ * ‖G t‖ ≤
        (delta * Complex.normSq (F t) + delta⁻¹ * Complex.normSq (G t)) / 2 := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      linarith [two_mul_le_add_mul_sq (a := ‖F t‖) (b := ‖G t‖) hdelta]
    calc
      ‖(gammaSymbol t : ℂ) * star (F t) * G t‖ =
          |gammaSymbol t| * (‖F t‖ * ‖G t‖) := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_star]
        ring
      _ ≤ (C * logWeight t) *
          ((delta * Complex.normSq (F t) + delta⁻¹ * Complex.normSq (G t)) / 2) :=
        mul_le_mul (hgamma t) hyoung (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (mul_nonneg hC (logWeight_nonneg t))
      _ = (C / 2) * (delta * (logWeight t * Complex.normSq (F t)) +
          delta⁻¹ * (logWeight t * Complex.normSq (G t))) := by ring
  calc
    ‖gammaMixed F G‖ = angularFactor *
        ‖∫ t : ℝ, (gammaSymbol t : ℂ) * star (F t) * G t‖ := by
      dsimp [gammaMixed]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos angularFactor_pos]
    _ ≤ angularFactor * ∫ t : ℝ, ‖(gammaSymbol t : ℂ) * star (F t) * G t‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) angularFactor_pos.le
    _ ≤ angularFactor * (∫ t : ℝ, (C / 2) *
        (delta * (logWeight t * Complex.normSq (F t)) +
         delta⁻¹ * (logWeight t * Complex.normSq (G t)))) :=
      mul_le_mul_of_nonneg_left hint angularFactor_pos.le
    _ = (C / 2) * (delta * logEnergy F + delta⁻¹ * logEnergy G) := by
      rw [integral_const_mul,
        integral_add (hWF.const_mul delta) (hWG.const_mul delta⁻¹),
        integral_const_mul, integral_const_mul]
      dsimp [logEnergy]
      ring

private theorem actual_gamma_quadratic_diagonal (F : ℝ → ℂ) :
    gammaMixed F F = (gammaQuadratic F : ℂ) := by
  have hid : (fun t : ℝ => (gammaSymbol t : ℂ) * star (F t) * F t) =
      fun t : ℝ => ((gammaSymbol t * Complex.normSq (F t) : ℝ) : ℂ) := by
    funext t
    calc
      (gammaSymbol t : ℂ) * star (F t) * F t =
          (gammaSymbol t : ℂ) * (F t * star (F t)) := by ring
      _ = ((gammaSymbol t * Complex.normSq (F t) : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_mul]
  change (angularFactor : ℂ) *
      (∫ t : ℝ, (gammaSymbol t : ℂ) * star (F t) * F t) =
    ((angularFactor * ∫ t : ℝ, gammaSymbol t * Complex.normSq (F t) : ℝ) : ℂ)
  rw [hid, integral_complex_ofReal, Complex.ofReal_mul]

private theorem actual_gamma_quadratic_add
    {C : ℝ} (hC : 0 ≤ C) (hgamma : ∀ t, |gammaSymbol t| ≤ C * logWeight t)
    {U E : ℝ → ℂ} (hU : Continuous U) (hE : Continuous E)
    (hWU : Integrable (fun t : ℝ => logWeight t * Complex.normSq (U t)))
    (hWE : Integrable (fun t : ℝ => logWeight t * Complex.normSq (E t))) :
    gammaQuadratic (fun t => U t + E t) - gammaQuadratic U =
      gammaQuadratic E + 2 * (gammaMixed U E).re := by
  have hGU : Integrable (fun t : ℝ => gammaSymbol t * Complex.normSq (U t)) :=
    integrable_actual_gamma_normSq_of_log_weight hU hWU
  have hGE : Integrable (fun t : ℝ => gammaSymbol t * Complex.normSq (E t)) :=
    integrable_actual_gamma_normSq_of_log_weight hE hWE
  have hM := integrable_actual_gamma_mixed hC hgamma hU hE hWU hWE
  have hSum : Integrable (fun t : ℝ => gammaSymbol t * Complex.normSq (U t) +
      gammaSymbol t * Complex.normSq (E t)) := hGU.add hGE
  have hMR : Integrable (fun t : ℝ =>
      ((gammaSymbol t : ℂ) * star (U t) * E t).re) := hM.re
  have hMRint : (∫ t : ℝ, ((gammaSymbol t : ℂ) * star (U t) * E t).re) =
      (∫ t : ℝ, (gammaSymbol t : ℂ) * star (U t) * E t).re := integral_re hM
  have hdecomp :
      (∫ t : ℝ, gammaSymbol t * Complex.normSq (U t + E t)) =
        (∫ t : ℝ, gammaSymbol t * Complex.normSq (U t)) +
        (∫ t : ℝ, gammaSymbol t * Complex.normSq (E t)) +
        2 * (∫ t : ℝ, (gammaSymbol t : ℂ) * star (U t) * E t).re := by
    calc
      _ = ∫ t : ℝ, gammaSymbol t * Complex.normSq (U t) +
          gammaSymbol t * Complex.normSq (E t) +
          2 * ((gammaSymbol t : ℂ) * star (U t) * E t).re := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [Complex.normSq_add, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
        ring
      _ = _ := by
        rw [integral_add hSum (hMR.const_mul 2),
          integral_add hGU hGE, integral_const_mul, hMRint]
  change angularFactor * (∫ t : ℝ, gammaSymbol t * Complex.normSq (U t + E t)) -
      angularFactor * (∫ t : ℝ, gammaSymbol t * Complex.normSq (U t)) =
    angularFactor * (∫ t : ℝ, gammaSymbol t * Complex.normSq (E t)) +
      2 * ((angularFactor : ℂ) *
        (∫ t : ℝ, (gammaSymbol t : ℂ) * star (U t) * E t)).re
  rw [hdecomp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

private theorem actual_gamma_quadratic_error_bound_at_constant
    {C : ℝ} (hC : 0 ≤ C) (hgamma : ∀ t, |gammaSymbol t| ≤ C * logWeight t)
    {U E : ℝ → ℂ} (hU : Continuous U) (hE : Continuous E)
    (hWU : Integrable (fun t : ℝ => logWeight t * Complex.normSq (U t)))
    (hWE : Integrable (fun t : ℝ => logWeight t * Complex.normSq (E t)))
    {delta : ℝ} (hdelta : 0 < delta) :
    |gammaQuadratic (fun t => U t + E t) - gammaQuadratic U| ≤
      C * ((1 + delta⁻¹) * logEnergy E + delta * logEnergy U) := by
  have hdiag := actual_gamma_mixed_young_bound hC hgamma hE hE hWE hWE
    (delta := 1) (by norm_num)
  rw [actual_gamma_quadratic_diagonal, Complex.norm_real, Real.norm_eq_abs] at hdiag
  have hdiag' : |gammaQuadratic E| ≤ C * logEnergy E := by
    calc
      |gammaQuadratic E| ≤ (C / 2) *
          (1 * logEnergy E + (1 : ℝ)⁻¹ * logEnergy E) := hdiag
      _ = C * logEnergy E := by norm_num; ring
  have hcross := actual_gamma_mixed_young_bound hC hgamma hU hE hWU hWE hdelta
  rw [actual_gamma_quadratic_add hC hgamma hU hE hWU hWE]
  calc
    |gammaQuadratic E + 2 * (gammaMixed U E).re| ≤
        |gammaQuadratic E| + 2 * |(gammaMixed U E).re| := by
      simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
        abs_add_le (gammaQuadratic E) (2 * (gammaMixed U E).re)
    _ ≤ C * logEnergy E + 2 * ‖gammaMixed U E‖ :=
      add_le_add hdiag' (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _)
        (by norm_num : (0 : ℝ) ≤ 2))
    _ ≤ C * logEnergy E + 2 * ((C / 2) *
        (delta * logEnergy U + delta⁻¹ * logEnergy E)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hcross (by norm_num : (0 : ℝ) ≤ 2))
    _ = C * ((1 + delta⁻¹) * logEnergy E + delta * logEnergy U) := by ring

/-- Actual completed-zeta Gamma quadratic continuity under logarithmically
weighted Fourier-square error. The actual symbol is the existing `Zeta23.mu`;
the conclusion introduces no substitute closed form or domain assertion. -/
theorem actual_gamma_quadratic_tendsto_of_log_weight_error
    {α : Type*} {l : Filter α} {U : ℝ → ℂ} {V : α → ℝ → ℂ}
    (hU : Continuous U)
    (hWU : Integrable (fun t : ℝ =>
      (1 + Real.log (1 + |t|)) * Complex.normSq (U t)))
    (hV : ∀ᶠ a in l, Continuous (V a))
    (hWE : ∀ᶠ a in l, Integrable (fun t : ℝ =>
      (1 + Real.log (1 + |t|)) * Complex.normSq (V a t - U t)))
    (hE : Tendsto (fun a => (1 / (2 * Real.pi)) * ∫ t : ℝ,
      (1 + Real.log (1 + |t|)) * Complex.normSq (V a t - U t)) l (𝓝 0)) :
    Tendsto (fun a => (1 / (2 * Real.pi)) * ∫ t : ℝ,
      (2 * Real.pi * Zeta23.mu t) * Complex.normSq (V a t)) l
      (𝓝 ((1 / (2 * Real.pi)) * ∫ t : ℝ,
        (2 * Real.pi * Zeta23.mu t) * Complex.normSq (U t))) := by
  obtain ⟨C, hC, hgamma⟩ := actual_gamma_log_growth
  have hgamma' : ∀ t, |gammaSymbol t| ≤ C * logWeight t := hgamma
  change Tendsto (fun a => logEnergy (fun t => V a t - U t)) l (𝓝 0) at hE
  change Tendsto (fun a => gammaQuadratic (V a)) l (𝓝 (gammaQuadratic U))
  rw [Metric.tendsto_nhds]
  intro eps heps
  let delta : ℝ := eps / (4 * C * (logEnergy U + 1))
  have hUfactor : 0 < logEnergy U + 1 := by linarith [logEnergy_nonneg U]
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hfixed : C * delta * logEnergy U < eps / 2 := by
    have hid : C * delta * (logEnergy U + 1) = eps / 4 := by
      dsimp [delta]
      field_simp [hC.ne', hUfactor.ne']
      <;> ring
    have hCd : 0 < C * delta := mul_pos hC hdelta
    nlinarith
  let rho : ℝ := eps / (2 * C * (1 + delta⁻¹))
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hev : ∀ᶠ a in l, logEnergy (fun t => V a t - U t) < rho :=
    (tendsto_order.1 hE).2 rho hrho
  filter_upwards [hV, hWE, hev] with a hVa hWEa hEa
  have hsmall : C * (1 + delta⁻¹) * logEnergy (fun t => V a t - U t) < eps / 2 := by
    have hden : 0 < 2 * C * (1 + delta⁻¹) := by positivity
    change logEnergy (fun t => V a t - U t) < eps / (2 * C * (1 + delta⁻¹)) at hEa
    have hlt := (lt_div_iff₀ hden).mp hEa
    nlinarith
  have hbound := actual_gamma_quadratic_error_bound_at_constant hC.le hgamma'
    hU (hVa.sub hU) hWU hWEa hdelta
  have hcancel : (fun t => U t + (V a t - U t)) = V a := by
    funext t
    ring
  change |gammaQuadratic (fun t => U t + (V a t - U t)) - gammaQuadratic U| ≤
    C * ((1 + delta⁻¹) * logEnergy (fun t => V a t - U t) + delta * logEnergy U)
    at hbound
  rw [hcancel] at hbound
  have hfinal : |gammaQuadratic (V a) - gammaQuadratic U| < eps :=
    lt_of_le_of_lt hbound (by nlinarith [hfixed, hsmall])
  simpa only [Real.dist_eq] using hfinal

end D5.S3.Weil.ZetaGamma.LogarithmicFormContinuity

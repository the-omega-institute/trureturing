/- GID: D5/S3/Weil/ZetaGamma/InverseSquareGammaConvergence
   generality: I
   mirror-B: none(waiver:analytic-dominated-convergence)
   mirror-E: none(waiver:actual-Gamma-symbol-continuity)
   anchors: []
   utility: none
   digest: Common inverse-square decay pays logarithmic and actual Gamma convergence. -/

import D5.S3.Weil.ZetaGamma.LogarithmicFormContinuity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

/-! A common Fourier envelope pays actual logarithmic domains, the full
weighted error limit and integrability of the original Gamma integrands. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaGamma.InverseSquareGammaConvergence

open MeasureTheory Filter
open scoped Topology
open D5.S3.Weil.ZetaGamma.LogarithmicFormContinuity
open private logWeight logWeight_nonneg integrable_actual_gamma_normSq_of_log_weight from
  D5.S3.Weil.ZetaGamma.LogarithmicFormContinuity

private theorem log_weight_continuous :
    Continuous (fun t : ℝ => 1 + Real.log (1 + |t|)) := by
  apply continuous_const.add
  have hi : Continuous (fun t : ℝ => 1 + |t|) := continuous_const.add continuous_abs
  exact hi.log (fun t => by positivity)

/-- The inverse quartic square makes the full logarithmic weight harmless.
The majorant is the already integrable Cauchy density, rather than an
unjustified assertion that a totalized Bochner integral is finite. -/
private theorem log_square_bound {D : ℝ}
    {f : ℝ → ℂ} (hf : ∀ t, ‖f t‖ ≤ D / (1 + t ^ (2 : ℕ))) (t : ℝ) :
    (1 + Real.log (1 + |t|)) * Complex.normSq (f t) ≤
      (2 * D ^ (2 : ℕ)) * (1 + t ^ (2 : ℕ))⁻¹ := by
  have hH : 0 < 1 + t ^ (2 : ℕ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + |t| by positivity)
  have hw : 1 + Real.log (1 + |t|) ≤ 2 * (1 + t ^ (2 : ℕ)) := by
    nlinarith [sq_nonneg (|t| - 1 / 2), sq_abs t]
  have hn : ‖f t‖ * (1 + t ^ (2 : ℕ)) ≤ D :=
    (le_div_iff₀ hH).mp (hf t)
  have hsq := pow_le_pow_left₀
    (mul_nonneg (norm_nonneg (f t)) hH.le) hn (2 : ℕ)
  have hmul := mul_le_mul_of_nonneg_right hw
    (mul_nonneg (sq_nonneg ‖f t‖) hH.le)
  rw [Complex.normSq_eq_norm_sq, ← div_eq_mul_inv]
  apply (le_div_iff₀ hH).2
  nlinarith only [hsq, hmul]

private theorem log_square_integrable {D : ℝ}
    {f : ℝ → ℂ} (hfc : Continuous f)
    (hf : ∀ t, ‖f t‖ ≤ D / (1 + t ^ (2 : ℕ))) :
    Integrable (fun t : ℝ =>
      (1 + Real.log (1 + |t|)) * Complex.normSq (f t)) := by
  apply (integrable_inv_one_add_sq.const_mul (2 * D ^ (2 : ℕ))).mono'
    ((log_weight_continuous.mul (Complex.continuous_normSq.comp hfc)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs]
  change |(1 + Real.log (1 + |t|)) * Complex.normSq (f t)| ≤ _
  rw [abs_of_nonneg
    (mul_nonneg (by simpa only [logWeight] using logWeight_nonneg t)
      (Complex.normSq_nonneg (f t)))]
  exact log_square_bound hf t

/-- Uniform inverse-square decay and pointwise convergence establish the
full logarithmic Fourier-square form limit and its actual completed-zeta
Gamma consequence. No log-moment or Gamma-domain premise is hidden here. -/
theorem actual_gamma_tendsto_of_uniform_inverse_square
    {U : ℝ → ℂ} {V : ℕ → ℝ → ℂ} {D : ℝ}
    (hU : Continuous U) (hV : ∀ n, Continuous (V n))
    (hbound : ∀ n t, ‖V n t‖ ≤ D / (1 + t ^ (2 : ℕ)))
    (hlim : ∀ t, Tendsto (fun n => V n t) atTop (𝓝 (U t))) :
    Integrable (fun t : ℝ =>
      (1 + Real.log (1 + |t|)) * Complex.normSq (U t)) ∧
    (∀ n, Integrable (fun t : ℝ =>
      (1 + Real.log (1 + |t|)) * Complex.normSq (V n t - U t))) ∧
    Tendsto (fun n => ∫ t : ℝ,
      (1 + Real.log (1 + |t|)) * Complex.normSq (V n t - U t)) atTop (𝓝 0) ∧
    Integrable (fun t : ℝ =>
      (2 * Real.pi * Zeta23.mu t) * Complex.normSq (U t)) ∧
    (∀ n, Integrable (fun t : ℝ =>
      (2 * Real.pi * Zeta23.mu t) * Complex.normSq (V n t))) ∧
    Tendsto (fun n => (1 / (2 * Real.pi)) * ∫ t : ℝ,
      (2 * Real.pi * Zeta23.mu t) * Complex.normSq (V n t)) atTop
      (𝓝 ((1 / (2 * Real.pi)) * ∫ t : ℝ,
        (2 * Real.pi * Zeta23.mu t) * Complex.normSq (U t))) := by
  have hUb (t : ℝ) : ‖U t‖ ≤ D / (1 + t ^ (2 : ℕ)) :=
    le_of_tendsto' (hlim t).norm (fun n => hbound n t)
  have hE (n : ℕ) (t : ℝ) :
      ‖V n t - U t‖ ≤ (2 * D) / (1 + t ^ (2 : ℕ)) := by
    calc
      _ ≤ ‖V n t‖ + ‖U t‖ := norm_sub_le _ _
      _ ≤ D / (1 + t ^ (2 : ℕ)) + D / (1 + t ^ (2 : ℕ)) :=
        add_le_add (hbound n t) (hUb t)
      _ = _ := by ring
  have hWU := log_square_integrable hU hUb
  have hWE (n : ℕ) : Integrable (fun t : ℝ =>
      (1 + Real.log (1 + |t|)) * Complex.normSq (V n t - U t)) :=
    log_square_integrable (f := fun t => V n t - U t) ((hV n).sub hU) (hE n)
  have hconv : Tendsto (fun n => ∫ t : ℝ,
      (1 + Real.log (1 + |t|)) * Complex.normSq (V n t - U t)) atTop (𝓝 0) := by
    have hdct := tendsto_integral_of_dominated_convergence
      (F := fun (n : ℕ) (t : ℝ) =>
        (1 + Real.log (1 + |t|)) * Complex.normSq (V n t - U t))
      (f := fun _ : ℝ => 0)
      (fun t : ℝ => (2 * (2 * D) ^ (2 : ℕ)) * (1 + t ^ (2 : ℕ))⁻¹)
      (fun n => (hWE n).aestronglyMeasurable)
      (integrable_inv_one_add_sq.const_mul (2 * (2 * D) ^ (2 : ℕ)))
      (fun n => Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (by simpa only [logWeight] using logWeight_nonneg t)
            (Complex.normSq_nonneg _))]
        exact log_square_bound (hE n) t)
      (Eventually.of_forall fun t => by
        have he : Tendsto (fun n => V n t - U t) atTop (𝓝 (0 : ℂ)) := by
          simpa only [sub_self] using (hlim t).sub
            (tendsto_const_nhds : Tendsto (fun _ : ℕ => U t) atTop (𝓝 (U t)))
        have hz := (Complex.continuous_normSq.tendsto 0).comp he
        simpa only [Function.comp_apply, Complex.normSq_zero, mul_zero] using
          hz.const_mul (1 + Real.log (1 + |t|)))
    simpa only [integral_zero] using hdct
  have hGU := integrable_actual_gamma_normSq_of_log_weight hU hWU
  have hGV (n : ℕ) := integrable_actual_gamma_normSq_of_log_weight
    (hV n) (log_square_integrable (hV n) (hbound n))
  refine ⟨hWU, hWE, hconv, hGU, hGV, ?_⟩
  exact actual_gamma_quadratic_tendsto_of_log_weight_error hU hWU
    (Eventually.of_forall hV) (Eventually.of_forall hWE)
    (by simpa only [mul_zero] using hconv.const_mul (1 / (2 * Real.pi)))

#print axioms actual_gamma_tendsto_of_uniform_inverse_square

end D5.S3.Weil.ZetaGamma.InverseSquareGammaConvergence

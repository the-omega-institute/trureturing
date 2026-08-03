/- GID: D5/S3/Fourier/PaleyWiener
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove the compact-support Fourier-Laplace transform is entire. -/

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace D5.S3.Fourier.PaleyWiener

open MeasureTheory
open scoped ContDiff

/-- A smooth, compactly supported function has an entire complex Fourier-Laplace
transform. This discharges the former `D5-T0018-C` classical-analysis debt:
the proof is native over pinned mathlib (differentiation under the integral via
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`). The proposition is
definitionally the one formerly registered as
`AxiomDebt.fourier_laplace_entire_classic`, and the
consumer `D5.S3.Weil.FourierLaplace.fourierLaplace_entire` closes under the
standard `{propext, Classical.choice, Quot.sound}` axioms only. -/
theorem fourier_laplace_entire_classic
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ ∞ g) (hcompact : HasCompactSupport g) :
    Differentiable ℂ (fun z : ℂ => ∫ x : ℝ, Complex.exp (-Complex.I * z * (x : ℂ)) * g x) := by
  intro z₀
  let F : ℂ → ℝ → ℂ := fun z x => Complex.exp (-Complex.I * z * (x : ℂ)) * g x
  let F' : ℂ → ℝ → ℂ := fun z x =>
    Complex.exp (-Complex.I * z * (x : ℂ)) * (-Complex.I * (x : ℂ)) * g x
  let bound : ℝ → ℝ := fun x =>
    Real.exp ((‖z₀‖ + 1) * ‖x‖) * ‖x‖ * ‖g x‖
  have hgcont : Continuous g := hsmooth.continuous
  have hFcont (z : ℂ) : Continuous (F z) := by
    dsimp [F]
    fun_prop
  have hFcompact (z : ℂ) : HasCompactSupport (F z) := by
    change HasCompactSupport ((fun x : ℝ =>
      Complex.exp (-Complex.I * z * (x : ℂ))) * g)
    exact hcompact.mul_left
  have hFint : Integrable (F z₀) :=
    (hFcont z₀).integrable_of_hasCompactSupport (hFcompact z₀)
  have hF'meas : AEStronglyMeasurable (F' z₀) := by
    apply Continuous.aestronglyMeasurable
    dsimp [F']
    fun_prop
  have hboundcont : Continuous bound := by
    dsimp [bound]
    fun_prop
  have hboundcompact : HasCompactSupport bound := by
    change HasCompactSupport ((fun x : ℝ =>
      Real.exp ((‖z₀‖ + 1) * ‖x‖) * ‖x‖) * fun x => ‖g x‖)
    exact hcompact.norm.mul_left
  have hboundint : Integrable bound :=
    hboundcont.integrable_of_hasCompactSupport hboundcompact
  have hbound : ∀ᵐ x : ℝ, ∀ z ∈ Metric.ball z₀ 1, ‖F' z x‖ ≤ bound x := by
    filter_upwards with x
    intro z hz
    have hz' : ‖z‖ < ‖z₀‖ + 1 := by
      have hdist : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
      calc
        ‖z‖ = ‖(z - z₀) + z₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ < 1 + ‖z₀‖ := by simpa [add_comm] using add_lt_add_right hdist ‖z₀‖
        _ = ‖z₀‖ + 1 := by ring
    have hre : (-Complex.I * z * (x : ℂ)).re ≤ (‖z₀‖ + 1) * ‖x‖ := by
      calc
        (-Complex.I * z * (x : ℂ)).re ≤ ‖-Complex.I * z * (x : ℂ)‖ :=
          Complex.re_le_norm _
        _ = ‖z‖ * ‖x‖ := by simp
        _ ≤ (‖z₀‖ + 1) * ‖x‖ :=
          mul_le_mul_of_nonneg_right hz'.le (norm_nonneg x)
    dsimp [F', bound]
    simp only [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Complex.norm_exp, one_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hre) (norm_nonneg x))
      (norm_nonneg (g x))
  have hdiff : ∀ᵐ x : ℝ, ∀ z ∈ Metric.ball z₀ 1,
      HasDerivAt (fun w => F w x) (F' z x) z := by
    filter_upwards with x
    intro z _hz
    have hinner : HasDerivAt (fun w : ℂ => -Complex.I * w * (x : ℂ))
        (-Complex.I * (x : ℂ)) z := by
      simpa using (((hasDerivAt_const z (-Complex.I)).mul (hasDerivAt_id z)).mul_const (x : ℂ))
    simpa [F, F', mul_assoc] using (hinner.cexp).mul_const (g x)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound)
    (Metric.ball_mem_nhds z₀ zero_lt_one)
    (Filter.Eventually.of_forall fun z => (hFcont z).aestronglyMeasurable)
    hFint hF'meas hbound hboundint hdiff
  simpa [F] using hmain.2.differentiableAt

end D5.S3.Fourier.PaleyWiener

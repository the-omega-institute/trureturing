/- GID: D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindowModel
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindowModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth-root bins realize the logarithmic square tail with positive weights. -/

import D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindow
import D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindowModel

/-! A positive-weight infinite spectrum for the logarithmic waiting gain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped Topology BigOperators

namespace D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindowModel

open OrdinateCounting (Spectrum)
open SpectrumCriticalMissingWindow (HasLogSquaredMass)
open SpectrumLogarithmicMissingWindow (HasLogarithmicSquareTail)
open SpectrumCriticalMissingWindowModel (exists_independent_bins modelWeight modelWeight_pos modelSpectrum
  eventually_model_mass model_square_tail_bound)

private theorem eventually_model_logarithmic_tail (g : ℕ → ℝ)
    (hg : ∀ n, 0 < g n ∧ (n : ℝ) + 1 < g n ^ 4 ∧ g n ^ 4 < (n : ℝ) + 2)
    (hinj : Function.Injective g) :
    HasLogarithmicSquareTail (modelSpectrum g hg hinj) modelWeight := by
  obtain ⟨B, hB, hbound⟩ := model_square_tail_bound g hg hinj
  refine ⟨B, hB, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (1 : ℝ)] with X hlog hX
  intro T _
  have hXpos := zero_lt_one.trans_le hX
  refine (hbound (fun a b => Classical.propDecidable (a = b)) X T hX).trans ?_
  rw [pow_two, ← div_div]
  exact div_le_div_of_nonneg_right
    ((div_le_self hB.le hX).trans (le_mul_of_one_le_right hB.le hlog)) hXpos.le

/-- The same fourth-root-bin weights realize the stronger square-tail hypothesis
on an infinite independent spectrum. -/
theorem exists_infinite_logarithmic_model :
    ∃ (S : Spectrum) (w : S.index → ℝ), Infinite S.index ∧
      (∀ j, 0 < w j) ∧ LinearIndependent ℚ S.gamma ∧
      HasLogSquaredMass S w ∧ HasLogarithmicSquareTail S w := by
  obtain ⟨g, hli, hg⟩ := exists_independent_bins
  let S := modelSpectrum g hg hli.injective
  exact ⟨S, modelWeight, inferInstanceAs (Infinite ℕ), modelWeight_pos, hli,
    eventually_model_mass g hg hli.injective, eventually_model_logarithmic_tail g hg hli.injective⟩

#print axioms exists_infinite_logarithmic_model

end D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindowModel

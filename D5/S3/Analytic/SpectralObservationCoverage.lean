/- GID: D5/S3/Analytic/SpectralObservationCoverage
   generality: G
   mirror-B: D5/B/S3/Analytic/SpectralObservationCoverage
   mirror-E: none(waiver:exact-observation-and-positive-measure-boundary)
   anchors: []
   utility: none
   digest: Dense observations certify a bounded low-energy map; normalized atomic measures defeat noisy gap classification. -/

import D5.S3.Analytic.PositiveLaplaceGap
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Observation coverage and noisy spectral certification

The first theorem states the precise extra bridge needed to infer vanishing
of an actual bounded low-energy map: a total observation family and genuine
finite measures whose low-energy masses equal squared observed-map norms.
No Hamiltonian or spectral theorem is silently supplied by that interface.

The counterexample reuses Mathlib's normalized Bernoulli measure. Both models
are probability measures, so an unobserved change of total spectral weight
cannot explain the obstruction. Even the complete noisy time trace does not
uniformly decide absence of subthreshold mass. See Section 13 of the existing
NS_OBSERVER_DYNAMICS_RH_THEORY.md for ordinary proofs and scope.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Analytic.SpectralObservationCoverage

open MeasureTheory Set ProbabilityTheory
open scoped NNReal
open D5.S3.Analytic.PositiveLaplaceGap

/-- A total observation family suffices once the actual low-energy
projection/mass identity has been established. This theorem does not construct
that projection or identify a physical Hamiltonian. -/
theorem total_observations_kill_low_map
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : E →L[ℝ] F) (obs : ι → E)
    (μ : ι → Measure ℝ≥0) [∀ i, IsFiniteMeasure (μ i)]
    (r : ℝ≥0) (Δ : ℝ) (hr : (r : ℝ) < Δ)
    (K : ι → ℝ) (hK : ∀ i, 0 ≤ K i)
    (htotal : Dense ((Submodule.span ℝ (range obs) : Submodule ℝ E) : Set E))
    (hmass : ∀ i, (μ i).real (Iic r) = ‖P (obs i)‖ ^ 2)
    (hdecay : ∀ i t, 0 ≤ t →
      laplaceCorrelation (μ i) t ≤ K i * Real.exp (-Δ * t)) :
    P = 0 := by
  have hkill : ∀ i, P (obs i) = 0 := by
    intro i
    have hz := subthreshold_mass_eq_zero (μ i) r Δ (K i) (hK i) hr (hdecay i)
    have hsq : ‖P (obs i)‖ ^ 2 = 0 := by
      rw [← hmass i, measureReal_def, hz, ENNReal.toReal_zero]
    have hn : ‖P (obs i)‖ = 0 := by nlinarith [norm_nonneg (P (obs i))]
    exact norm_eq_zero.mp hn
  have hspan : Submodule.span ℝ (range obs) ≤ LinearMap.ker P.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hkill i
  have hsub : ((Submodule.span ℝ (range obs) : Submodule ℝ E) : Set E) ⊆
      {x : E | P x = 0} := hspan
  have hclosed : IsClosed {x : E | P x = 0} :=
    isClosed_eq P.continuous continuous_const
  have hclosure := closure_minimal hsub hclosed
  rw [htotal.closure_eq] at hclosure
  ext x
  exact hclosure (mem_univ x)

/-- Actual normalized measures with different subthreshold masses have
uniformly close Laplace correlations at every nonnegative time. -/
theorem normalized_hidden_atom (lo r hi : ℝ≥0)
    (η : Set.Icc (0 : ℝ) 1) (hlr : lo ≤ r) (hrh : r < hi) :
    (Measure.dirac hi).real (Iic r) = 0 ∧
    (bernoulliMeasure lo hi η).real (Iic r) = (η : ℝ) ∧
    ∀ t : ℝ, 0 ≤ t →
      |laplaceCorrelation (bernoulliMeasure lo hi η) t -
        laplaceCorrelation (Measure.dirac hi) t| ≤ (η : ℝ) := by
  have hhi : hi ∉ Iic r := not_le.mpr hrh
  constructor
  · simp [measureReal_def, Measure.dirac_apply, measurableSet_Iic, hhi]
  constructor
  · exact bernoulliMeasure_real_apply_of_mem_of_notMem η measurableSet_Iic hlr hhi
  · intro t ht
    have hformula : laplaceCorrelation (bernoulliMeasure lo hi η) t -
        laplaceCorrelation (Measure.dirac hi) t =
        (η : ℝ) * (Real.exp (-t * (lo : ℝ)) - Real.exp (-t * (hi : ℝ))) := by
      unfold laplaceCorrelation
      rw [integral_bernoulliMeasure, integral_dirac]
      simp only [smul_eq_mul]
      ring
    have horder : Real.exp (-t * (hi : ℝ)) ≤ Real.exp (-t * (lo : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left
        (show (lo : ℝ) ≤ (hi : ℝ) from hlr.trans hrh.le) (neg_nonpos.mpr ht)
    have hone : Real.exp (-t * (lo : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) lo.property)
    have hdiff : Real.exp (-t * (lo : ℝ)) - Real.exp (-t * (hi : ℝ)) ≤ 1 := by
      linarith [Real.exp_pos (-t * (hi : ℝ))]
    rw [hformula, abs_of_nonneg (mul_nonneg η.property.1 (sub_nonneg.mpr horder))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiff η.property.1

/-- No predicate on even the entire time trace uniformly certifies zero
subthreshold mass under positive uniform absolute error. The witness uses
probability measures and midpoint data, with error η/2 on both models. -/
theorem no_uniform_noisy_gap_classifier (lo r hi : ℝ≥0)
    (η : Set.Icc (0 : ℝ) 1) (hη : 0 < (η : ℝ))
    (hlr : lo ≤ r) (hrh : r < hi) :
    ¬ ∃ decide : (ℝ → ℝ) → Prop,
      ∀ μ : Measure ℝ≥0, IsProbabilityMeasure μ → ∀ y : ℝ → ℝ,
        (∀ t : ℝ, 0 ≤ t → |y t - laplaceCorrelation μ t| ≤ (η : ℝ) / 2) →
        (decide y ↔ μ.real (Iic r) = 0) := by
  rintro ⟨decide, hdecide⟩
  obtain ⟨hm0, hm1, hclose⟩ := normalized_hidden_atom lo r hi η hlr hrh
  let y : ℝ → ℝ := fun t =>
    (laplaceCorrelation (Measure.dirac hi) t +
      laplaceCorrelation (bernoulliMeasure lo hi η) t) / 2
  have hnoise0 : ∀ t : ℝ, 0 ≤ t →
      |y t - laplaceCorrelation (Measure.dirac hi) t| ≤ (η : ℝ) / 2 := by
    intro t ht
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hclose t ht)
    dsimp [y]
    apply abs_le.mpr
    constructor <;> linarith
  have hnoise1 : ∀ t : ℝ, 0 ≤ t →
      |y t - laplaceCorrelation (bernoulliMeasure lo hi η) t| ≤ (η : ℝ) / 2 := by
    intro t ht
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hclose t ht)
    dsimp [y]
    apply abs_le.mpr
    constructor <;> linarith
  have hd : decide y :=
    (hdecide (Measure.dirac hi) inferInstance y hnoise0).mpr hm0
  have hz := (hdecide (bernoulliMeasure lo hi η) inferInstance y hnoise1).mp hd
  rw [hm1] at hz
  linarith

#print axioms total_observations_kill_low_map
#print axioms normalized_hidden_atom
#print axioms no_uniform_noisy_gap_classifier

end D5.S3.Analytic.SpectralObservationCoverage

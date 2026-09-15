/- GID: D5/S3/Analytic/CalibratedLaplaceBand
   generality: G
   mirror-B: D5/B/S3/Analytic/CalibratedLaplaceBand
   mirror-E: none(waiver:exact-positive-measure-extremizers)
   anchors: []
   utility: none
   digest: Calibrated band mass gives a linear noise bound, attained by normalized two-atom measures. -/

import D5.S3.Analytic.PositiveLaplaceGap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Calibrated Laplace observations on an energy band

The lower estimate retains the measured mass of the larger band instead of
throwing it away. Its normalized, bounded-band consequence is an exact
extremal reduction for ANY set of nonnegative observation times. In the
half-band case one actual observation gives mass <= 4*epsilon + tau.

The coefficient four is attained under probability normalization and exact
band support. The tail coefficient is not asserted sharp. No physical
Hamiltonian, ultraviolet cutoff, or Yang--Mills identification is assumed.

Background: Bertsimas--Popescu, SIAM J. Optim. 15(3), 2005,
DOI 10.1137/S1052623401399903, concerns extremal probability inequalities.
The concrete proofs here use pinned Mathlib and the existing Laplace integral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Analytic.CalibratedLaplaceBand

open MeasureTheory Set ProbabilityTheory
open scoped NNReal
open D5.S3.Analytic.PositiveLaplaceGap

/-- A positive threshold determines a single calibrated observation time. -/
def halfBandTime (r : ℝ≥0) : ℝ := Real.log 2 / (r : ℝ)

/-- At this time the kernels at r and 2r are respectively one half and one quarter. -/
theorem halfBandTime_spec (r : ℝ≥0) (hr : 0 < (r : ℝ)) :
    0 ≤ halfBandTime r ∧
    Real.exp (-halfBandTime r * (r : ℝ)) = (1 / 2 : ℝ) ∧
    Real.exp (-halfBandTime r * ((2 * r : ℝ≥0) : ℝ)) = (1 / 4 : ℝ) := by
  have ht : 0 ≤ halfBandTime r :=
    div_nonneg (Real.log_nonneg (by norm_num)) hr.le
  have harg : -halfBandTime r * (r : ℝ) = -Real.log 2 := by
    dsimp [halfBandTime]
    field_simp [ne_of_gt hr] <;> ring
  have hfirst : Real.exp (-halfBandTime r * (r : ℝ)) = (1 / 2 : ℝ) := by
    rw [harg, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  refine ⟨ht, hfirst, ?_⟩
  have hdouble : -halfBandTime r * ((2 * r : ℝ≥0) : ℝ) =
      -halfBandTime r * (r : ℝ) + -halfBandTime r * (r : ℝ) := by
    push_cast
    ring
  rw [hdouble, Real.exp_add, hfirst]
  norm_num

private theorem kernel_integrable (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun E : ℝ≥0 => Real.exp (-t * (E : ℝ))) μ := by
  have hc : Continuous (fun E : ℝ≥0 => Real.exp (-t * (E : ℝ))) := by fun_prop
  apply (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable
  exact ae_of_all _ fun E => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) E.property)

/-- A two-step simple function below the actual Laplace kernel retains both
nested band masses. No global support or probability assumption is needed. -/
theorem band_mass_lower (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (r R : ℝ≥0) (hrR : r ≤ R) (t : ℝ) (ht : 0 ≤ t) :
    μ.real (Iic r) * (Real.exp (-t * (r : ℝ)) - Real.exp (-t * (R : ℝ))) +
      μ.real (Iic R) * Real.exp (-t * (R : ℝ)) ≤ laplaceCorrelation μ t := by
  classical
  let a : ℝ := Real.exp (-t * (r : ℝ)) - Real.exp (-t * (R : ℝ))
  let b : ℝ := Real.exp (-t * (R : ℝ))
  let f : ℝ≥0 → ℝ := (Iic r).indicator (fun _ => a)
  let g : ℝ≥0 → ℝ := (Iic R).indicator (fun _ => b)
  have hf : Integrable f μ := (integrable_const a).indicator measurableSet_Iic
  have hg : Integrable g μ := (integrable_const b).indicator measurableSet_Iic
  have hpoint : ∀ E : ℝ≥0, f E + g E ≤ Real.exp (-t * (E : ℝ)) := by
    intro E
    by_cases hEr : E ≤ r
    · have hER : E ≤ R := hEr.trans hrR
      have hm := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
        (show (E : ℝ) ≤ (r : ℝ) from hEr) (neg_nonpos.mpr ht))
      simpa [f, g, a, b, hEr, hER] using hm
    · by_cases hER : E ≤ R
      · have hm := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
          (show (E : ℝ) ≤ (R : ℝ) from hER) (neg_nonpos.mpr ht))
        simpa [f, g, b, hEr, hER] using hm
      · simpa [f, g, hEr, hER] using (Real.exp_pos (-t * (E : ℝ))).le
  have hmono := integral_mono (hf.add hg) (kernel_integrable μ t ht) hpoint
  have hfi : (∫ E, f E ∂μ) = μ.real (Iic r) * a := by
    dsimp [f]
    rw [integral_indicator measurableSet_Iic]
    simp
  have hgi : (∫ E, g E ∂μ) = μ.real (Iic R) * b := by
    dsimp [g]
    rw [integral_indicator measurableSet_Iic]
    simp
  simp only [Pi.add_apply] at hmono
  rw [integral_add hf hg, hfi, hgi] at hmono
  exact hmono

/-- Under probability normalization and unit mass in [0,R], every prescribed
low-band mass is feasible exactly when the two endpoint atoms are feasible.
This holds simultaneously for arbitrary nonnegative-time upper envelopes. -/
theorem normalized_band_feasible_iff_two_atoms (r R : ℝ≥0) (hrR : r < R)
    (m : Set.Icc (0 : ℝ) 1) (times : Set ℝ) (U : ℝ → ℝ)
    (htimes : ∀ t ∈ times, 0 ≤ t) :
    (∃ μ : Measure ℝ≥0, IsProbabilityMeasure μ ∧
      μ.real (Iic R) = 1 ∧ μ.real (Iic r) = (m : ℝ) ∧
      ∀ t ∈ times, laplaceCorrelation μ t ≤ U t) ↔
    (∀ t ∈ times, (m : ℝ) * Real.exp (-t * (r : ℝ)) +
      (1 - (m : ℝ)) * Real.exp (-t * (R : ℝ)) ≤ U t) := by
  constructor
  · rintro ⟨μ, hprob, hband, hmass, hobs⟩
    letI : IsProbabilityMeasure μ := hprob
    intro t ht
    have h := (band_mass_lower μ r R hrR.le t (htimes t ht)).trans (hobs t ht)
    rw [hband, hmass] at h
    nlinarith
  · intro h
    refine ⟨bernoulliMeasure r R m, inferInstance, ?_, ?_, ?_⟩
    · exact bernoulliMeasure_real_apply_of_mem_of_mem m measurableSet_Iic hrR.le
        (mem_Iic.mpr le_rfl)
    · exact bernoulliMeasure_real_apply_of_mem_of_notMem m measurableSet_Iic
        (mem_Iic.mpr le_rfl) (not_le.mpr hrR)
    · intro t ht
      simpa only [laplaceCorrelation, integral_bernoulliMeasure, smul_eq_mul] using h t ht

/-- A single calibrated observation bounds low-band mass linearly in absolute
noise and in missing high-band mass. M is a known reference mass, not a hidden
probability normalization. For probability measures take M=1. -/
theorem calibrated_half_band_bound (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (r : ℝ≥0) (hr : 0 < (r : ℝ)) (M ε τ : ℝ)
    (hband : M - τ ≤ μ.real (Iic (2 * r)))
    (hobs : laplaceCorrelation μ (halfBandTime r) ≤ M / 4 + ε) :
    μ.real (Iic r) ≤ 4 * ε + τ := by
  obtain ⟨ht, hfirst, hsecond⟩ := halfBandTime_spec r hr
  have hrR : r ≤ 2 * r := by
    have := r.property
    exact_mod_cast (by linarith : (r : ℝ) ≤ 2 * (r : ℝ))
  have h := (band_mass_lower μ r (2 * r) hrR (halfBandTime r) ht).trans hobs
  rw [hfirst, hsecond] at h
  linarith

/-- The normalized two-atom measure attains the coefficient four exactly.
Its entire nonnegative-time trace lies within m/4 of the reference exp(-2rt),
and the discrepancy equals m/4 at the declared observation time. -/
theorem normalized_half_band_sharp (r : ℝ≥0) (hr : 0 < (r : ℝ))
    (m : Set.Icc (0 : ℝ) 1) :
    let μ := bernoulliMeasure r (2 * r) m
    μ.real (Iic r) = (m : ℝ) ∧ μ.real (Iic (2 * r)) = 1 ∧
      (∀ t : ℝ, 0 ≤ t →
        0 ≤ laplaceCorrelation μ t - Real.exp (-t * ((2 * r : ℝ≥0) : ℝ)) ∧
        laplaceCorrelation μ t - Real.exp (-t * ((2 * r : ℝ≥0) : ℝ)) ≤ (m : ℝ) / 4) ∧
      laplaceCorrelation μ (halfBandTime r) - (1 / 4 : ℝ) = (m : ℝ) / 4 := by
  dsimp only
  have hrR : r < 2 * r := by
    exact_mod_cast (by linarith : (r : ℝ) < 2 * (r : ℝ))
  have hformula (t : ℝ) :
      laplaceCorrelation (bernoulliMeasure r (2 * r) m) t =
        (m : ℝ) * Real.exp (-t * (r : ℝ)) +
          (1 - (m : ℝ)) * Real.exp (-t * ((2 * r : ℝ≥0) : ℝ)) := by
    simp only [laplaceCorrelation, integral_bernoulliMeasure, smul_eq_mul]
  refine ⟨bernoulliMeasure_real_apply_of_mem_of_notMem m measurableSet_Iic
    (mem_Iic.mpr le_rfl) (not_le.mpr hrR),
    bernoulliMeasure_real_apply_of_mem_of_mem m measurableSet_Iic hrR.le
      (mem_Iic.mpr le_rfl), ?_, ?_⟩
  · intro t ht
    let s := Real.exp (-t * (r : ℝ))
    have hs0 : 0 ≤ s := (Real.exp_pos _).le
    have hs1 : s ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) r.property)
    have hdouble : Real.exp (-t * ((2 * r : ℝ≥0) : ℝ)) = s ^ 2 := by
      dsimp [s]
      rw [pow_two, ← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [hformula, hdouble]
    change 0 ≤ (m : ℝ) * s + (1 - (m : ℝ)) * s ^ 2 - s ^ 2 ∧
      (m : ℝ) * s + (1 - (m : ℝ)) * s ^ 2 - s ^ 2 ≤ (m : ℝ) / 4
    have hlo : 0 ≤ s - s ^ 2 := by nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
    have hhi : s - s ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith [sq_nonneg (s - 1 / 2)]
    constructor
    · nlinarith [mul_nonneg m.property.1 hlo]
    · nlinarith [mul_le_mul_of_nonneg_left hhi m.property.1]
  · obtain ⟨_, hfirst, hsecond⟩ := halfBandTime_spec r hr
    rw [hformula, hfirst, hsecond]
    ring

#print axioms halfBandTime
#print axioms halfBandTime_spec
#print axioms band_mass_lower
#print axioms normalized_band_feasible_iff_two_atoms
#print axioms calibrated_half_band_bound
#print axioms normalized_half_band_sharp

end D5.S3.Analytic.CalibratedLaplaceBand

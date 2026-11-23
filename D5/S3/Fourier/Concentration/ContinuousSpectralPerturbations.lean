/- GID: D5/S3/Fourier/Concentration/ContinuousSpectralPerturbations
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/ContinuousSpectralPerturbations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Interval averaging bounds the near-collisions of a perturbed spectrum. -/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.ProductMeasure

/-! Closed near-collision bands on continuous perturbation intervals. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations

private def intervalNoise (radius : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (2 * radius))⁻¹ • volume.restrict (Icc (-radius) radius)

private theorem intervalNoise_probability {radius : ℝ} (hradius : 0 < radius) :
    IsProbabilityMeasure (intervalNoise radius) := by
  constructor
  have hlen : radius - -radius = 2 * radius := by ring
  rw [intervalNoise, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Icc, hlen]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

private theorem intervalNoise_affine_local {radius a b η : ℝ}
    (hradius : 0 < radius) (ha : a ≠ 0) :
    intervalNoise radius {x | |a * x + b| ≤ η} ≤ ENNReal.ofReal (η / (|a| * radius)) := by
  let center := -b / a
  let reach := η / |a|
  have hfactor (x : ℝ) : a * x + b = a * (x - center) := by
    dsimp [center]
    field_simp
    ring
  have hset : {x : ℝ | |a * x + b| ≤ η} = Icc (center - reach) (center + reach) := by
    ext x
    change |a * x + b| ≤ η ↔ _
    rw [hfactor, abs_mul, mul_comm |a|, ← le_div_iff₀ (abs_pos.mpr ha), abs_le]
    change -reach ≤ x - center ∧ x - center ≤ reach ↔ _
    rw [mem_Icc, le_sub_iff_add_le, sub_le_iff_le_add, neg_add_eq_sub, add_comm reach]
  have hlen : center + reach - (center - reach) = 2 * reach := by ring
  have hmeasure : volume (Icc (center - reach) (center + reach) ∩
      Icc (-radius) radius) ≤ ENNReal.ofReal (2 * reach) := by
    calc
      _ ≤ volume (Icc (center - reach) (center + reach)) := measure_mono inter_subset_left
      _ = _ := by rw [Real.volume_Icc, hlen]
  rw [hset, intervalNoise, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Icc, smul_eq_mul]
  calc
    _ ≤ (ENNReal.ofReal (2 * radius))⁻¹ * ENNReal.ofReal (2 * reach) :=
      by gcongr
    _ = ENNReal.ofReal (reach / radius) := by
      rw [mul_comm, ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (by positivity)]
      congr 1
      field_simp
    _ = _ := by simp [reach, div_div]

private theorem intervalNoise_fin_affine {n : ℕ} (radius a : Fin (n + 1) → ℝ)
    (b η : ℝ) (hradius : ∀ j, 0 < radius j) (i : Fin (n + 1)) (ha : a i ≠ 0) :
    (Measure.pi fun j => intervalNoise (radius j))
      {x | |(∑ j, a j * x j) + b| ≤ η} ≤ ENNReal.ofReal (η / (|a i| * radius i)) := by
  let μ (j : Fin (n + 1)) := intervalNoise (radius j)
  have (j : Fin (n + 1)) : IsProbabilityMeasure (μ j) := intervalNoise_probability (hradius j)
  let ν := Measure.pi fun j : Fin n => μ (i.succAbove j)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let rest (y : Fin n → ℝ) := (∑ j : Fin n, a (i.succAbove j) * y j) + b
  let S := {xy : ℝ × (Fin n → ℝ) | |a i * xy.1 + rest xy.2| ≤ η}
  have hS : MeasurableSet S := by
    change MeasurableSet {xy : ℝ × (Fin n → ℝ) | |a i * xy.1 + rest xy.2| ≤ η}
    apply measurableSet_le _ measurable_const
    unfold rest
    fun_prop
  have hpre : e ⁻¹' S = {x | |(∑ j, a j * x j) + b| ≤ η} := by
    ext x
    change |a i * x i + rest (fun j => x (i.succAbove j))| ≤ η ↔
      |(∑ j, a j * x j) + b| ≤ η
    simp only [rest, i.sum_univ_succAbove (f := fun j => a j * x j), add_assoc]
  have hp : MeasurePreserving e (Measure.pi μ) ((μ i).prod ν) :=
    measurePreserving_piFinSuccAbove μ i
  rw [← hpre, ← Measure.map_apply hp.measurable hS, hp.map_eq, Measure.prod_apply_symm hS]
  calc
    _ ≤ ∫⁻ _, ENNReal.ofReal (η / (|a i| * radius i)) ∂ν := by
      apply lintegral_mono
      intro y
      change intervalNoise (radius i) {x | |a i * x + rest y| ≤ η} ≤ _
      exact intervalNoise_affine_local (b := rest y) (η := η) (hradius i) ha
    _ = _ := by simp [ν]

end D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations

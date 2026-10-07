/- GID: D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Final
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/Lemma43Final
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Contact.Lemma43Close
import D5.S3.Arith.Lattices.Klartag.Completion.Threshold2

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Real
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open scoped ENNReal NNReal

theorem integrableOn_profile_radial_t {a₀ α W T : ℝ} {n : ℕ} (hW : 0 ≤ W) (hT : 0 ≤ T) :
    IntegrableOn (fun y : ℝ => y ^ (n - 1) * ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t y)
      (Ioi (0 : ℝ)) := by
  have hsm : StronglyMeasurable (fun y : ℝ => ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t y) :=
    ((measurable_profile_uncurry (a₀ := a₀) (α := α) (W := W) (n := n)).comp
      measurable_swap).stronglyMeasurable.integral_prod_right'
  have hbnd : ∀ y : ℝ, ‖∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t y‖ ≤ 1 / 2 * T := by
    intro y
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) T)
      (C := 1 / 2) (f := fun t => profile a₀ α W n t y)
      (by simp [Real.volume_Ioc]) (fun t _ => norm_profile_le t y)
    simpa [Real.volume_Ioc, max_eq_left hT] using h
  refine integrableOn_Ioi_of_support hW ?_ ?_
  · refine integrableOn_of_bounded' measurableSet_Ioc (by simp [Real.volume_Ioc])
      (((measurable_id.pow_const (n - 1)).stronglyMeasurable.mul hsm).aestronglyMeasurable)
      (M := W ^ (n - 1) * (1 / 2 * T)) ?_
    intro y hy
    have hy0 : (0 : ℝ) ≤ y := hy.1.le
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hy0 _)]
    exact mul_le_mul (pow_le_pow_left₀ hy0 hy.2 _) (hbnd y) (norm_nonneg _)
      (pow_nonneg (le_trans hy0 hy.2) _)
  · intro y hy
    simp [profile_zero_of_gt hy]

end D5.S3.Arith.Lattices.Klartag

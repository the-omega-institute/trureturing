/- GID: D5/S3/Arith/Congruence/ConditionalComparison/CappedGainDistortion
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Sharp actual-load bounds for the physical distortion. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/CappedGainDistortion.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.CappedGainDepth
import D5.S3.Arith.Congruence.ConditionalComparison.Distortion

/-!
# Sharp actual-load bounds for the physical distortion

The threshold is fixed before the current coordinate is exposed. The bound
retains the actual eligible ending load instead of replacing it by a fixed cap.
-/

namespace Erdos7

theorem insideMultiplier_le_natural {δ α : ℚ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    insideMultiplier δ α ≤ (1 - min α δ)⁻¹ := by
  by_cases h : α ≤ δ
  · simp only [insideMultiplier, h, if_true, min_eq_left h]
    exact inv_nonneg.mpr (by linarith)
  · rw [min_eq_right (le_of_not_ge h)]
    exact insideMultiplier_le hδ0 hδ1 hα0 hα1

theorem outsideMultiplier_eq_natural (δ α : ℚ) :
    outsideMultiplier δ α = (1 - min α δ)⁻¹ := by
  by_cases h : α ≤ δ
  · simp [outsideMultiplier, h, min_eq_left h]
  · simp [outsideMultiplier, h, min_eq_right (le_of_not_ge h)]

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem distort_prob_le_natural (μ : FiniteLaw Ω) (A B : Ω → Prop)
    [DecidablePred A] [DecidablePred B] (δ : ℚ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (μ.distort A δ hδ0 hδ1).prob B ≤
      μ.prob B * (1 - min (μ.prob A) δ)⁻¹ := by
  let M := (1 - min (μ.prob A) δ)⁻¹
  have hweight : ∀ ω, (μ.distort A δ hδ0 hδ1).weight ω ≤ μ.weight ω * M := by
    intro ω
    rw [distort_weight]
    apply mul_le_mul_of_nonneg_left _ (μ.weight_nonneg ω)
    split_ifs
    · exact insideMultiplier_le_natural hδ0 hδ1 (μ.prob_nonneg A) (μ.prob_le_one A)
    · exact (outsideMultiplier_eq_natural δ (μ.prob A)).le
  change (∑ ω, (μ.distort A δ hδ0 hδ1).weight ω * (if B ω then 1 else 0)) ≤
    (∑ ω, μ.weight ω * (if B ω then 1 else 0)) * M
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hB : B ω
  · simpa only [hB, if_true, mul_one] using hweight ω
  · simp [hB]

end FiniteLaw

namespace CappedGain

theorem thresholdMass_le_load {θ q t L α : ℚ}
    (ht0 : 0 ≤ t) (htq : t < q) (hqθ : q ≤ θ) (hload : θ * α ≤ L) :
    thresholdMass (t / θ) α ≤ charge q t L := by
  have hθ : 0 < θ := by linarith
  have hc : 0 < q - t := by linarith
  have hθt : 0 < θ - t := by linarith
  by_cases h : α ≤ t / θ
  · simp only [thresholdMass, h, if_true]
    exact charge_nonneg htq L
  · simp only [thresholdMass, h, if_false]
    have he : (α - t / θ) / (1 - t / θ) = (θ * α - t) / (θ - t) := by
      field_simp
    rw [he]
    calc
      (θ * α - t) / (θ - t) ≤ max (L - t) 0 / (θ - t) :=
        div_le_div_of_nonneg_right ((sub_le_sub_right hload t).trans (le_max_left _ _)) hθt.le
      _ ≤ max (L - t) 0 / (q - t) :=
        div_le_div_of_nonneg_left (le_max_right _ _) hc (by linarith)

theorem natural_denominator_bound {θ q t L α : ℚ}
    (ht0 : 0 ≤ t) (htq : t < q) (hqθ : q ≤ θ) (hload : θ * α ≤ L) :
    q - min t L ≤ θ * (1 - min α (t / θ)) := by
  have hθ : 0 < θ := by linarith
  have he : θ * min α (t / θ) = min (θ * α) t := by
    rw [mul_min_of_nonneg _ _ hθ.le]
    congr 1
    field_simp
  have hm : min (θ * α) t ≤ min L t := min_le_min_right t hload
  rw [min_comm t L]
  nlinarith

/-- Generic physical one-block prefix bound. The original prefix mass is
bounded by `b/θ`; the distorted mass is bounded using the actual ending load. -/
theorem distorted_prefix_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (A B : Ω → Prop) [DecidablePred A] [DecidablePred B]
    {θ q t L b : ℚ} (ht0 : 0 ≤ t) (htq : t < q) (hqθ : q ≤ θ)
    (hb : 0 ≤ b) (hload : θ * μ.prob A ≤ L) (hprefix : μ.prob B ≤ b / θ) :
    (μ.distort A (t / θ)
      (by
        have hθ : 0 < θ := by linarith
        exact div_nonneg ht0 hθ.le)
      (by
        have hθ : 0 < θ := by linarith
        exact (div_lt_one hθ).mpr (by linarith))).prob B ≤
      b * rho q t L := by
  have hθ : 0 < θ := by linarith
  have hδ0 : 0 ≤ t / θ := div_nonneg ht0 hθ.le
  have hδ1 : t / θ < 1 := (div_lt_one hθ).mpr (by linarith)
  have hm : 0 < 1 - min (μ.prob A) (t / θ) := by
    linarith [min_le_right (μ.prob A) (t / θ)]
  have hden := natural_denominator_bound ht0 htq hqθ hload
  have hqmin : 0 < q - min t L := by linarith [min_le_left t L]
  calc
    (μ.distort A (t / θ) hδ0 hδ1).prob B ≤
        μ.prob B * (1 - min (μ.prob A) (t / θ))⁻¹ :=
      μ.distort_prob_le_natural A B _ hδ0 hδ1
    _ ≤ (b / θ) * (1 - min (μ.prob A) (t / θ))⁻¹ :=
      mul_le_mul_of_nonneg_right hprefix (inv_nonneg.mpr hm.le)
    _ = b / (θ * (1 - min (μ.prob A) (t / θ))) := by field_simp
    _ ≤ b / (q - min t L) := div_le_div_of_nonneg_left hb hqmin hden
    _ = b * rho q t L := by unfold rho; ring

/-- Comparison between actual and reference primes uses only ordered-field
algebra. Actual ending weights are not individually replaced. -/
theorem prime_prefix_cap_mono {p P z : ℚ} (hp : 1 ≤ p) (hpP : p ≤ P)
    (hz : 0 ≤ z) (hzp : z < p - 2) (d : ℕ) :
    beta P d / (P - 2 - z) ≤ beta p d / (p - 2 - z) := by
  have hp0 : 0 < p := by linarith
  have hP0 : 0 < P := by linarith
  have hdp : 0 < p - 2 - z := by linarith
  have hdP : 0 < P - 2 - z := by linarith
  have hpow : (1 : ℚ) / P ^ d ≤ 1 / p ^ d :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hp0 d)
      (pow_le_pow_left₀ hp0.le hpP d)
  have hquot : (1 + z) / (P - 2 - z) ≤ (1 + z) / (p - 2 - z) :=
    div_le_div_of_nonneg_left (by linarith) hdp (by linarith)
  have hpw0 : 0 ≤ (1 : ℚ) / P ^ d := by positivity
  have hfac0 : 0 ≤ 1 + (1 + z) / (p - 2 - z) := by positivity
  have hprod := mul_le_mul hpow (add_le_add_right hquot 1)
    (show 0 ≤ 1 + (1 + z) / (P - 2 - z) by positivity)
    (show 0 ≤ (1 : ℚ) / p ^ d by positivity)
  have heP : beta P d / (P - 2 - z) =
      (1 / P ^ d) * (1 + (1 + z) / (P - 2 - z)) := by
    unfold beta
    field_simp
    <;> ring
  have hep : beta p d / (p - 2 - z) =
      (1 / p ^ d) * (1 + (1 + z) / (p - 2 - z)) := by
    unfold beta
    field_simp
    <;> ring
  rw [heP, hep]
  exact hprod

end CappedGain
end Erdos7

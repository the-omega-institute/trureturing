/- GID: D5/S3/Arith/GoldenLayerMarginalDecay
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenLayerMarginalDecay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime-layer marginals are geometrically bounded and decay below every positive price. -/

import D5.S3.Arith.GoldenResourceOptimalInteger
import Mathlib.Analysis.SpecificLimits.Basic

/- Library-search audit trail (2026-09-06):
   * Repository searches for `goldenLayerMarginal`, `golden_layer_marginal`,
     `layer_marginal`, and marginal bound variants found the definition, the frozen strict
     decrease theorem, and its use by `GoldenLocalThreshold`, but no quantitative bound or
     convergence theorem for these prime layers.
   * Pinned Mathlib searches for logarithmic one-minus-power ratio bounds found the generic
     `Real.log_le_sub_one_of_pos` and `tendsto_pow_atTop_nhds_zero_of_lt_one`, but no theorem
     specializing them to `(1 - x^(a+1)) / (1 - x^a)`.
   * Searches of the other pinned Lean packages (`batteries`, `aesop`, `plausible`,
     `proofwidgets`, `Qq`, `LeanSearchClient`, `importGraph`, and `Cli`) found no matching
     logarithmic ratio bound.
   * A GitHub Lean code search was attempted through the discovered NyxID `api-github`
     service, but the service returned `API key is failed`; broader online ecosystem search is
     therefore ASSUMED-UNVERIFIED. -/

namespace D5.S3.Arith.GoldenLayerMarginalDecay

open D5.S3.Arith.GoldenResourceOptimalInteger

noncomputable section

private theorem layer_ratio_sub_one_le {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    (1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹ ^ a) - 1 ≤ (p : ℝ)⁻¹ ^ a := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpInvPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpPos
  have hpInvLt : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
  have hpowNonneg : 0 ≤ (p : ℝ)⁻¹ ^ a := pow_nonneg hpInvPos.le a
  have hpowLeInv : (p : ℝ)⁻¹ ^ a ≤ (p : ℝ)⁻¹ := by
    simpa only [pow_one] using pow_le_pow_of_le_one hpInvPos.le hpInvLt.le ha
  have hden : 0 < 1 - (p : ℝ)⁻¹ ^ a :=
    sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega))
  rw [sub_le_iff_le_add, div_le_iff₀ hden, pow_succ]
  have hmul := mul_le_mul_of_nonneg_left hpowLeInv hpowNonneg
  nlinarith

/-- A positive prime layer is bounded by its reciprocal geometric scale divided by `log p`. -/
theorem golden_layer_marginal_le_inv_pow {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    goldenLayerMarginal p a ≤ (p : ℝ)⁻¹ ^ a / Real.log p := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpInvPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpPos
  have hpInvLt : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
  have hden : 0 < 1 - (p : ℝ)⁻¹ ^ a :=
    sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega))
  have hnum : 0 < 1 - (p : ℝ)⁻¹ ^ (a + 1) :=
    sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega))
  have hlog :
      Real.log ((1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹ ^ a)) ≤
        (1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹ ^ a) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hnum hden)
  unfold goldenLayerMarginal
  apply (div_le_div_iff_of_pos_right (Real.log_pos (by exact_mod_cast hp.one_lt))).mpr
  exact hlog.trans (layer_ratio_sub_one_le hp ha)

/-- At every positive price, the marginals for a fixed prime eventually lie below that price. -/
theorem golden_layer_marginal_lt_of_le {p : ℕ} (hp : p.Prime)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ N : ℕ, ∀ a : ℕ, N ≤ a → goldenLayerMarginal p a < lambda := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpInvPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpPos
  have hpInvLt : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
  have hdecay : Filter.Tendsto (fun a : ℕ => (p : ℝ)⁻¹ ^ a / Real.log p)
      Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hpInvPos.le hpInvLt).div_const (Real.log p)
  have heventually : ∀ᶠ a : ℕ in Filter.atTop,
      (p : ℝ)⁻¹ ^ a / Real.log p < lambda :=
    (tendsto_order.1 hdecay).2 lambda hlambda
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventually
  refine ⟨max N 1, fun a ha => ?_⟩
  exact (golden_layer_marginal_le_inv_pow hp (le_trans (Nat.le_max_right N 1) ha)).trans_lt
    (hN a (le_trans (Nat.le_max_left N 1) ha))

end

end D5.S3.Arith.GoldenLayerMarginalDecay

/- GID: D5/S3/Arith/GoldenPrimeLayerCofinite
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenPrimeLayerCofinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A uniform prime cutoff places every positive layer marginal below a fixed positive price. -/

import D5.S3.Arith.GoldenLayerMarginalDecay

/- Library-search audit trail (2026-09-06):
   * Repository searches for `goldenLayerMarginal`, `marginal_lt_of_prime`, and
     prime/cofinite variants found the definition and the fixed-prime bounds in
     `GoldenLayerMarginalDecay`, but no uniform cutoff across primes.
   * Pinned Mathlib searches for reciprocal and logarithmic limits found
     `tendsto_inv_atTop_nhds_zero_nat`, `Real.tendsto_log_atTop`,
     `tendsto_natCast_atTop_atTop`, and `Filter.Tendsto.inv_tendsto_atTop`; these
     are used directly below. No theorem packaging the target cutoff was found.
   * Online Lean ecosystem searches through NyxID found `plby/lean-proofs` using
     the same Mathlib limit ingredients, plus Mathlib mirrors and unrelated Lean
     sources, but no declaration matching this uniform prime-layer cutoff. -/

namespace D5.S3.Arith.GoldenPrimeLayerCofinite

open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLayerMarginalDecay

noncomputable section

private theorem inv_pow_div_log_lt {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → (p : ℝ)⁻¹ / Real.log p < lambda := by
  have hinv :
      Filter.Tendsto (fun p : ℕ => (p : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hlog :
      Filter.Tendsto (fun p : ℕ => Real.log (p : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlimit :
      Filter.Tendsto (fun p : ℕ => (p : ℝ)⁻¹ / Real.log p)
        Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinv.mul hlog.inv_tendsto_atTop
  obtain ⟨P, hP⟩ := Filter.eventually_atTop.mp ((tendsto_order.1 hlimit).2 lambda hlambda)
  exact ⟨P, hP⟩

/-- Beyond a uniform prime cutoff, every positive layer marginal is below the price. -/
theorem golden_layer_marginal_lt_of_prime_le {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p → ∀ a : ℕ, 1 ≤ a →
      goldenLayerMarginal p a < lambda := by
  obtain ⟨P, hP⟩ := inv_pow_div_log_lt hlambda
  refine ⟨P, fun p hp hpP a ha => ?_⟩
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpInvPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpPos
  have hpInvLt : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
  have hpowLeInv : (p : ℝ)⁻¹ ^ a ≤ (p : ℝ)⁻¹ := by
    simpa only [pow_one] using pow_le_pow_of_le_one hpInvPos.le hpInvLt.le ha
  have hratio : (p : ℝ)⁻¹ ^ a / Real.log p ≤ (p : ℝ)⁻¹ / Real.log p :=
    (div_le_div_iff_of_pos_right (Real.log_pos (by exact_mod_cast hp.one_lt))).mpr hpowLeInv
  exact (golden_layer_marginal_le_inv_pow hp ha).trans_lt
    (hratio.trans_lt (hP p hpP))

end

end D5.S3.Arith.GoldenPrimeLayerCofinite

/- GID: D5/S3/TotalVariation/NegentropyBudget
   generality: G
   mirror-B: D5/B/S3/TotalVariation/NegentropyBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound distance from the uniform law by the finite Shannon entropy deficit. -/

/- Library-search audit trail (2026-08-11):
   * Local pinned-mathlib grep terms: `Pinsker`, `totalVariation`, `total variation`,
     `entropy_le_log_card`, `klDiv.*uniform`, `uniform.*klDiv`, `le_sqrt_of_sq_le`,
     `le_sqrt`, `sq_sqrt`, and `sqrt_le_sqrt`.
   * Pinned mathlib has the square-root order lemmas used below, but no matching finite-real
     total-variation/Pinsker theorem or finite uniform-divergence/Shannon-entropy identity.
   * Repository HIT: `Pinsker.pinsker_inequality`,
     `EntropyDivergenceIdentity.kl_divergence_uniform_eq`, and
     `Metric.total_variation_nonneg` compose directly to prove the result. No analytic estimate
     is re-proved here.
   * Repository MISS: no declaration or Blueprint definition named `muStar`, `mu_star`, or
     state-dependent tunable sharpness exists. `ObserverMetric.perturbationSeminorm` instead
     measures the update defect of a permutation and an observable, so it is not substituted for
     that missing quantity. No density-matrix/von-Neumann-entropy bridge is available either.
   * The total-variation DPI applies one channel to both input masses. Without a theorem that the
     relevant forgetting channel preserves the uniform law, it does not establish monotonicity of
     this uniform-reference budget. That separate clause is therefore not claimed here.
-/

import D5.S3.Entropy.EntropyDivergenceIdentity
import D5.S3.TotalVariation.Metric

namespace D5.S3.TotalVariation.NegentropyBudget

open D5.S3.Entropy.EntropyDivergenceIdentity
open D5.S3.Entropy.MaxEntropy
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

/-- Twice the total variation of a finite probability mass from the uniform law is bounded by
the square root of twice its Shannon entropy deficit. All logarithms and entropies are in nats. -/
theorem total_variation_uniform_le_sqrt_entropy_deficit
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ι → ℝ) (hr : (∀ i, 0 ≤ r i) ∧ ∑ i, r i = 1) :
    2 * totalVariation r (fun _ => (Fintype.card ι : ℝ)⁻¹) ≤
      Real.sqrt (2 * (Real.log (Fintype.card ι) - shannonEntropy r)) := by
  classical
  let u : ι → ℝ := fun _ => (Fintype.card ι : ℝ)⁻¹
  have hcard_pos : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hu : (∀ i, 0 ≤ u i) ∧ ∑ i, u i = 1 := by
    constructor
    · intro i
      exact (inv_pos.mpr hcard_pos).le
    · simp [u, hcard_ne]
  have hac : ∀ i, u i = 0 → r i = 0 := by
    intro i hui
    exact ((inv_ne_zero hcard_ne) hui).elim
  have hpinsker := pinsker_inequality r u hr hu hac
  have hidentity :
      D5.S3.Divergence.ClassicalDPI.klDivergence r u =
        Real.log (Fintype.card ι) - shannonEntropy r := by
    simpa [u] using kl_divergence_uniform_eq r hr
  rw [hidentity] at hpinsker
  have htv_nonneg : 0 ≤ totalVariation r u := total_variation_nonneg r u
  apply Real.le_sqrt_of_sq_le
  nlinarith

end D5.S3.TotalVariation.NegentropyBudget

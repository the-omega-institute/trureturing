/- GID: D5/S3/Entropy/EntropyDivergenceIdentity
   generality: G
   mirror-B: D5/B/S3/Entropy/EntropyDivergenceIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pin finite Shannon entropy to KL divergence from the uniform law. -/

/- Library-search audit trail (2026-08-09):
   * Local pinned-mathlib grep terms: `klDiv_compProd_eq_add`, `toReal_klDiv`,
     `klDiv.*uniform`, `uniform.*klDiv`, `relativeEntropy.*uniform`,
     `uniform.*relativeEntropy`, `shannonEntropy`, `shannon_entropy`,
     `finiteEntropy`, `entropy_le_log_card`, `entropy.*Fintype`,
     `Fintype.*entropy`, `negMulLog.*Finset`, and `Finset.*negMulLog`.
   * Pinned mathlib provides measure-valued KL identities and the scalar `Real.negMulLog`,
     but no finite uniform-divergence/Shannon-entropy identity matching this statement was found.
   * Repository-wide `D5/` grep terms: `kl_divergence_uniform_eq`,
     `klDivergence.*Fintype.card`, `Fintype.card.*klDivergence`,
     `shannonEntropy.*klDivergence`, `klDivergence.*shannonEntropy`,
     rearrangements of `Real.log (Fintype.card _) - shannonEntropy`,
     `negMulLog` with `Fintype.card`, and the expanded KL summand.
   * `MaxEntropy.entropy_le_log_card` already proves this relation internally as a
     `have hidentity`; that local fact is not a reusable public theorem. This file intentionally
     re-proves the same termwise identity against the imported repository definitions.
-/

import D5.S3.Entropy.MaxEntropy

namespace D5.S3.Entropy.EntropyDivergenceIdentity

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Entropy.MaxEntropy

/-- KL divergence from the uniform law is the log-cardinality entropy deficit. -/
theorem kl_divergence_uniform_eq {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → ℝ) (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) :
    klDivergence p (fun _ => (Fintype.card ι : ℝ)⁻¹) =
      Real.log (Fintype.card ι) - shannonEntropy p := by
  classical
  have hcard_pos : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hterm (i : ι) :
      p i * Real.log (p i / (Fintype.card ι : ℝ)⁻¹) =
        -Real.negMulLog (p i) + Real.log (Fintype.card ι) * p i := by
    by_cases hpi : p i = 0
    · simp [hpi]
    · rw [show p i / (Fintype.card ι : ℝ)⁻¹ =
        p i * (Fintype.card ι : ℝ) by simp]
      rw [Real.log_mul hpi hcard_ne]
      simp only [Real.negMulLog]
      ring
  rw [klDivergence, shannonEntropy]
  calc
    (∑ i, p i * Real.log (p i / (Fintype.card ι : ℝ)⁻¹)) =
        ∑ i, (-Real.negMulLog (p i) + Real.log (Fintype.card ι) * p i) := by
          exact Finset.sum_congr rfl fun i _ => hterm i
    _ = -(∑ i, Real.negMulLog (p i)) +
        Real.log (Fintype.card ι) * ∑ i, p i := by
          rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
    _ = Real.log (Fintype.card ι) - ∑ i, Real.negMulLog (p i) := by
          rw [hp.2]
          ring

end D5.S3.Entropy.EntropyDivergenceIdentity

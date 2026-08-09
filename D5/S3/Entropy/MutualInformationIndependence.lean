/- GID: D5/S3/Entropy/MutualInformationIndependence
   generality: G
   mirror-B: D5/B/S3/Entropy/MutualInformationIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize vanishing finite mutual information by independence. -/

/- Library-search audit trail (2026-08-09):
   * Local pinned-mathlib grep terms: `mutualInformation`, `mutual_information`,
     `mutualInfo`, `MutualInfo`, `klDiv_eq_zero_iff`, `independence`, and `independent`.
   * `Mathlib.InformationTheory.KullbackLeibler.Basic` provides the measure-valued converse
     Gibbs theorem `InformationTheory.klDiv_eq_zero_iff`, but no pinned finite
     mutual-information definition or bridge to the repository's real-valued finite sum was
     found.
   * Repository-wide `D5/` grep terms: the mutual-information names above; `independence` and
     `independent`; `marginal` adjacent to products; `klDivergence` adjacent to zero; and the
     displayed product-of-own-marginals equality in both orientations. No duplicate was found.
   * `MutualInformationProduct.mutual_information_product_eq_zero` is the other direction in a
     specialized form: it starts with normalized factors and proves that their product has zero
     mutual information. The theorem below starts with an arbitrary normalized joint law and
     characterizes vanishing by equality with the product of that joint law's own marginals.
   * The proof therefore reuses `MutualInformation.mutualInformation`, `ChainRule.marginal`, and
     `GibbsEquality.kl_divergence_eq_zero_iff`, mirroring the three reference-law premise
     discharges in `MutualInformation.mutual_information_nonneg`. Units are nats because the
     imported divergence uses `Real.log`.
   * Program significance: nonnegativity alone holds for any admissible reference, while
     vanishing on products constrains the definition only on the product submanifold. This
     converse constrains the reference wherever mutual information vanishes; together with the
     wave-18 entropy decomposition, the cluster is pinned beyond product laws.
-/

import D5.S3.Divergence.GibbsEquality
import D5.S3.Entropy.MutualInformation

namespace D5.S3.Entropy.MutualInformationIndependence

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.ChainRule
open D5.S3.Divergence.GibbsEquality
open D5.S3.Entropy.MutualInformation

/-- Mutual information vanishes exactly when a normalized finite joint law is the product of
its own marginals. -/
theorem mutual_information_eq_zero_iff_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    mutualInformation p = 0
      ↔ p = fun q : ι × κ =>
          marginal p q.1 * marginal (fun r : κ × ι => p (r.2, r.1)) q.2 := by
  classical
  have hmarginal_fst_nonneg (i : ι) : 0 ≤ marginal p i := by
    rw [marginal]
    exact Finset.sum_nonneg fun j _ => hp.1 (i, j)
  have hmarginal_snd_nonneg (j : κ) :
      0 ≤ marginal (fun r : κ × ι => p (r.2, r.1)) j := by
    rw [marginal]
    exact Finset.sum_nonneg fun i _ => hp.1 (i, j)
  have hmarginal_fst_sum : ∑ i, marginal p i = 1 := by
    simp only [marginal]
    rw [← Fintype.sum_prod_type]
    exact hp.2
  have hmarginal_snd_sum :
      ∑ j, marginal (fun r : κ × ι => p (r.2, r.1)) j = 1 := by
    simp only [marginal]
    rw [Finset.sum_comm, ← Fintype.sum_prod_type]
    exact hp.2
  rw [mutualInformation]
  apply kl_divergence_eq_zero_iff
  · exact hp
  · constructor
    · intro q
      exact mul_nonneg (hmarginal_fst_nonneg q.1) (hmarginal_snd_nonneg q.2)
    · simp only [Fintype.sum_prod_type]
      rw [← Fintype.sum_mul_sum, hmarginal_fst_sum, hmarginal_snd_sum, one_mul]
  · intro q hproduct
    rcases mul_eq_zero.mp hproduct with hfst | hsnd
    · apply le_antisymm
      · apply le_trans _ (le_of_eq hfst)
        rw [marginal]
        exact Finset.single_le_sum (fun j _ => hp.1 (q.1, j)) (Finset.mem_univ q.2)
      · exact hp.1 q
    · apply le_antisymm
      · apply le_trans _ (le_of_eq hsnd)
        rw [marginal]
        exact Finset.single_le_sum (fun i _ => hp.1 (i, q.2)) (Finset.mem_univ q.1)
      · exact hp.1 q

end D5.S3.Entropy.MutualInformationIndependence

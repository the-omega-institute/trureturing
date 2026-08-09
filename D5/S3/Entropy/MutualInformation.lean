/- GID: D5/S3/Entropy/MutualInformation
   generality: G
   mirror-B: D5/B/S3/Entropy/MutualInformation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define finite classical mutual information in nats and prove it is nonnegative. -/

/- Library-search audit trail (2026-08-09):
   * Local pinned-mathlib grep terms: `mutualInformation`, `mutual_information`,
     `mutualInfo`, `MutualInfo`, `mutual information`, `finite.*entropy`,
     `entropy.*Fintype`, `klDiv`, `toReal_klDiv`, and `klDiv_compProd_eq_add`.
   * `Mathlib.InformationTheory.KullbackLeibler` provides measure-valued KL divergence in
     `ℝ≥0∞`, but no finite mutual-information definition or pinned bridge identifying that
     divergence with the repository's real-valued finite sum was found.
   * Repository-wide `D5/` grep terms: the mutual-information names above; `product reference`,
     `product distribution`, `joint distribution`, `independence`, and `independent`;
     `marginal` adjacent to products or `klDivergence`; and KL inequalities in `0 ≤ ...`,
     `... ≥ 0`, `sub_nonneg`, and both inequality orientations. No duplicate was found.
   * `MarginalMonotone.kl_divergence_marginal_le` and
     `ProductAdditivity.kl_divergence_product_additive` are respectively a marginal inequality
     and a product equality, not nonnegativity of joint-to-own-marginals KL.
   * The definition below therefore reuses the repository's `klDivergence` and `marginal` as
     their single sources. Units are nats because `klDivergence` uses `Real.log`.
-/

import D5.S3.Divergence.ChainRule
import D5.S3.Divergence.GrandmotherTheorem

namespace D5.S3.Entropy.MutualInformation

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.ChainRule
open D5.S3.Divergence.GrandmotherTheorem

/-- Finite classical mutual information in nats: joint KL divergence from the product of
its first-coordinate marginal and its swapped second-coordinate marginal. -/
noncomputable def mutualInformation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) : ℝ :=
  klDivergence p
    (fun q => marginal p q.1 * marginal (fun r : κ × ι => p (r.2, r.1)) q.2)

/-- Mutual information of a finite nonnegative normalized joint mass function is nonnegative. -/
theorem mutual_information_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    0 ≤ mutualInformation p := by
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
  apply kl_divergence_nonneg
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

end D5.S3.Entropy.MutualInformation

/- GID: D5/S3/Entropy/MutualInformationProduct
   generality: G
   mirror-B: D5/B/S3/Entropy/MutualInformationProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pin finite mutual information to zero on normalized product laws. -/

/- Library-search audit trail (2026-08-09):
   * Local pinned-mathlib grep terms: `mutualInformation`, `mutual_information`,
     `mutualInfo`, `MutualInfo`, `mutual information`, `klDiv.*prod`,
     `klDiv.*compProd`, `klDiv.*eq_zero`, `toReal_klDiv`, `PMF.*klDiv`,
     `Fintype.sum_mul_sum`, and `Real.log_one`.
   * `Mathlib.InformationTheory.KullbackLeibler.ChainRule` provides the measure-valued
     product/chain rules `InformationTheory.klDiv_compProd_left` and
     `InformationTheory.klDiv_compProd_eq_add`; `KullbackLeibler.Basic` provides
     `InformationTheory.klDiv_eq_zero_iff`. No pinned finite mutual-information definition or
     bridge to the repository's real-valued finite sum was found.
   * Repository-wide `D5/` grep terms: the mutual-information names above; `product reference`,
     `product distribution`, `joint distribution`, `independent`; `marginal` adjacent to products,
     multiplication, or `klDivergence`; `klDivergence` adjacent to zero; swapped functions using
     `.2` and `.1`; `Fintype.sum_mul_sum`; and `Finset.mul_sum`.
   * `MutualInformation.mutual_information_nonneg`,
     `ProductAdditivity.kl_divergence_product_additive`, and
     `GibbsEquality.kl_divergence_eq_zero_iff` are adjacent results, but none evaluates both own
     marginals of a product joint, including the swapped second marginal. No duplicate was found.
   * The proof below therefore evaluates both imported `marginal`s explicitly and then unfolds the
     imported `mutualInformation` and `klDivergence` definitions.
-/

import D5.S3.Entropy.MutualInformation

namespace D5.S3.Entropy.MutualInformationProduct

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.MutualInformation

/-- Mutual information vanishes on a product of normalized finite mass functions. -/
theorem mutual_information_product_eq_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ)
    (ha : (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1) (hb : (∀ j, 0 ≤ b j) ∧ ∑ j, b j = 1) :
    mutualInformation (fun q : ι × κ => a q.1 * b q.2) = 0 := by
  classical
  have hfirst_marginal :
      marginal (fun q : ι × κ => a q.1 * b q.2) = a := by
    funext i
    simp only [marginal]
    calc
      (∑ j, a i * b j) = a i * ∑ j, b j := by rw [Finset.mul_sum]
      _ = a i := by rw [hb.2, mul_one]
  have hswapped_second_marginal :
      marginal (fun r : κ × ι =>
        (fun q : ι × κ => a q.1 * b q.2) (r.2, r.1)) = b := by
    funext j
    simp only [marginal]
    calc
      (∑ i, a i * b j) = (∑ i, a i) * b j := by rw [Finset.sum_mul]
      _ = b j := by rw [ha.2, one_mul]
  have hproduct_nonneg (q : ι × κ) : 0 ≤ a q.1 * b q.2 :=
    mul_nonneg (ha.1 q.1) (hb.1 q.2)
  have hzero_mass_term (q : ι × κ) :
      a q.1 * b q.2 * Real.log (a q.1 * b q.2 / (a q.1 * b q.2)) = 0 := by
    by_cases hmass : a q.1 * b q.2 = 0
    · simp [hmass]
    · have hmass_pos : 0 < a q.1 * b q.2 :=
        lt_of_le_of_ne (hproduct_nonneg q) (Ne.symm hmass)
      rw [div_self (ne_of_gt hmass_pos), Real.log_one, mul_zero]
  rw [mutualInformation, hfirst_marginal, hswapped_second_marginal, klDivergence]
  exact Finset.sum_eq_zero fun q _ => hzero_mass_term q

end D5.S3.Entropy.MutualInformationProduct

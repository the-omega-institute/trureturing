/- GID: D5/S3/Divergence/ProductAdditivity
   generality: G
   mirror-B: D5/B/S3/Divergence/ProductAdditivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove additivity of finite classical KL divergence under product distributions. -/

/- Library-search audit trail (2026-08-09):
   * Local pinned-mathlib grep terms: `klDiv.*prod`, `prod.*klDiv`,
     `product.*divergence`, `relativeEntropy.*prod`, `Fintype.sum_prod_type`,
     and `Real.log_mul`.
   * `Mathlib.InformationTheory.KullbackLeibler.ChainRule` provides the measure-valued
     chain rule `InformationTheory.klDiv_compProd_eq_add`. No pinned theorem was found
     that identifies its `ENNReal`-valued measure divergence with the repository's
     real-valued finite sum on product mass functions, so applying it would not be a thin wrapper.
   * The proof below instead uses the exact upstream algebraic lemmas
     `Fintype.sum_prod_type` and `Real.log_mul`, while importing the repository's single-source
     `ClassicalDPI.klDivergence` rather than redefining divergence.
-/

import D5.S3.Divergence.ClassicalDPI

namespace D5.S3.Divergence.ProductAdditivity

open D5.S3.Divergence.ClassicalDPI

/-- Classical KL divergence is additive on products of strictly positive finite probability
mass functions. The reference functions need only be strictly positive, not normalized. -/
theorem kl_divergence_product_additive
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b : ι → ℝ) (a' b' : κ → ℝ)
    (ha : ∑ i, a i = 1) (ha' : ∑ j, a' j = 1)
    (hapos : ∀ i, 0 < a i) (hbpos : ∀ i, 0 < b i)
    (ha'pos : ∀ j, 0 < a' j) (hb'pos : ∀ j, 0 < b' j) :
    klDivergence (fun p : ι × κ => a p.1 * a' p.2)
        (fun p : ι × κ => b p.1 * b' p.2) =
      klDivergence a b + klDivergence a' b' := by
  classical
  simp only [klDivergence, Fintype.sum_prod_type]
  have hratio (i : ι) (j : κ) :
      a i * a' j / (b i * b' j) = (a i / b i) * (a' j / b' j) := by
    field_simp [ne_of_gt (hbpos i), ne_of_gt (hb'pos j)]
  calc
    (∑ i, ∑ j, a i * a' j * Real.log (a i * a' j / (b i * b' j))) =
        ∑ i, ∑ j,
          (a i * a' j * Real.log (a i / b i) +
            a i * a' j * Real.log (a' j / b' j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hratio, Real.log_mul
        (ne_of_gt (div_pos (hapos i) (hbpos i)))
        (ne_of_gt (div_pos (ha'pos j) (hb'pos j)))]
      ring
    _ = (∑ i, ∑ j, a i * a' j * Real.log (a i / b i)) +
        ∑ i, ∑ j, a i * a' j * Real.log (a' j / b' j) := by
      simp only [Finset.sum_add_distrib]
    _ = (∑ i, a i * Real.log (a i / b i) * ∑ j, a' j) +
        ∑ j, a' j * Real.log (a' j / b' j) * ∑ i, a i := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = (∑ i, a i * Real.log (a i / b i)) +
        ∑ j, a' j * Real.log (a' j / b' j) := by
      rw [ha, ha']
      simp

end D5.S3.Divergence.ProductAdditivity

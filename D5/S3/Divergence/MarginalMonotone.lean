/- GID: D5/S3/Divergence/MarginalMonotone
   generality: G
   mirror-B: D5/B/S3/Divergence/MarginalMonotone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove marginalization monotonicity for finite classical KL divergence. -/

/- Library-search audit trail (2026-08-09):
   * Local pinned-mathlib grep terms: `klDiv.*(map|mono|le|marg|fst|snd|prod)`,
     `dataProcessing`, `Fintype.*klDiv`, `PMF.*klDiv`, `toReal_klDiv`,
     `klDiv.*toReal`, `relativeEntropy`, and `Kullback.*finite`.
   * `Mathlib.InformationTheory.KullbackLeibler.ChainRule` provides the measure-valued
     chain rule `InformationTheory.klDiv_compProd_eq_add`; its divergence takes values in
     `ℝ≥0∞` and its conditional term is expressed through measure kernels.
   * `Mathlib.InformationTheory.KullbackLeibler.Basic` provides `toReal_klDiv` integral
     identities, but no pinned theorem was found that identifies those integrals with the
     repository's real-valued finite sum or its quotient conditionals.
   * The proof below therefore composes the repository's finite-sum chain rule with its
     finite-sum Gibbs inequality, without rebuilding either result.
-/

import D5.S3.Divergence.ChainRule
import D5.S3.Divergence.GrandmotherTheorem

namespace D5.S3.Divergence.MarginalMonotone

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.ChainRule
open D5.S3.Divergence.GrandmotherTheorem

/-- Marginalization cannot increase classical KL divergence for strictly positive finite
joint mass functions. -/
theorem kl_divergence_marginal_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p q : ι × κ → ℝ) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x) :
    klDivergence (marginal p) (marginal q) ≤ klDivergence p q := by
  classical
  rw [kl_divergence_chain_rule p q hp hq]
  cases isEmpty_or_nonempty κ with
  | inl hκ =>
      letI := hκ
      simp [klDivergence]
  | inr hκ =>
      letI := hκ
      have hMarginalPPos (i : ι) : 0 < marginal p i := by
        rw [marginal]
        refine Finset.sum_pos' (fun j _ => (hp (i, j)).le) ?_
        let j : κ := Classical.choice inferInstance
        exact ⟨j, Finset.mem_univ j, hp (i, j)⟩
      have hMarginalQPos (i : ι) : 0 < marginal q i := by
        rw [marginal]
        refine Finset.sum_pos' (fun j _ => (hq (i, j)).le) ?_
        let j : κ := Classical.choice inferInstance
        exact ⟨j, Finset.mem_univ j, hq (i, j)⟩
      have hConditionalPPos (i : ι) (j : κ) : 0 < conditional p i j := by
        exact div_pos (hp (i, j)) (hMarginalPPos i)
      have hConditionalQPos (i : ι) (j : κ) : 0 < conditional q i j := by
        exact div_pos (hq (i, j)) (hMarginalQPos i)
      have hConditionalSumP (i : ι) : ∑ j, conditional p i j = 1 := by
        simp only [conditional]
        rw [← Finset.sum_div, ← marginal]
        exact div_self (ne_of_gt (hMarginalPPos i))
      have hConditionalSumQ (i : ι) : ∑ j, conditional q i j = 1 := by
        simp only [conditional]
        rw [← Finset.sum_div, ← marginal]
        exact div_self (ne_of_gt (hMarginalQPos i))
      apply le_add_of_nonneg_right
      refine Finset.sum_nonneg ?_
      intro i _
      apply mul_nonneg (hMarginalPPos i).le
      apply kl_divergence_nonneg
      · exact ⟨fun j => (hConditionalPPos i j).le, hConditionalSumP i⟩
      · exact ⟨fun j => (hConditionalQPos i j).le, hConditionalSumQ i⟩
      · intro j hqj
        exact (ne_of_gt (hConditionalQPos i j) hqj).elim

end D5.S3.Divergence.MarginalMonotone

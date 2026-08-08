/- GID: D5/S3/Divergence/ChainRule
   generality: G
   mirror-B: D5/B/S3/Divergence/ChainRule
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove the chain rule for finite classical KL divergence. -/

/- Library-search audit trail (2026-08-09):
   * Local pinned-mathlib grep terms: `klDiv_compProd_eq_add`, `klDiv.*sum`,
     `Fintype.*klDiv`, `PMF.*klDiv`, `klDiv.*toReal`, `toReal.*klDiv`,
     `Kullback.*finite`, `relativeEntropy`, `Fintype.sum_prod_type`, and `Real.log_mul`.
   * `Mathlib.InformationTheory.KullbackLeibler.ChainRule` provides the measure-valued
     chain rule `InformationTheory.klDiv_compProd_eq_add`.
   * `Mathlib.InformationTheory.KullbackLeibler.Basic` provides general `toReal_klDiv`
     integral identities, but no pinned theorem was found that evaluates those measure integrals
     as the repository's real-valued finite sum, including its displayed conditional term.
   * The proof below therefore works directly with the repository's single-source
     `ClassicalDPI.klDivergence`, using the pinned algebraic lemmas `Fintype.sum_prod_type`
     and `Real.log_mul`.
-/

import D5.S3.Divergence.ClassicalDPI

namespace D5.S3.Divergence.ChainRule

open D5.S3.Divergence.ClassicalDPI

/-- The first-coordinate marginal of a finite joint mass function. -/
noncomputable def marginal {ι κ : Type*} [Fintype κ]
    (r : ι × κ → ℝ) (i : ι) : ℝ :=
  ∑ j, r (i, j)

/-- The second-coordinate conditional mass function at a first-coordinate value. -/
noncomputable def conditional {ι κ : Type*} [Fintype κ]
    (r : ι × κ → ℝ) (i : ι) (j : κ) : ℝ :=
  r (i, j) / marginal r i

/-- The chain rule for classical KL divergence of strictly positive finite joint mass functions. -/
theorem kl_divergence_chain_rule
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p q : ι × κ → ℝ)
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x) :
    klDivergence p q =
      klDivergence (marginal p) (marginal q) +
        ∑ i, marginal p i *
          klDivergence (conditional p i) (conditional q i) := by
  classical
  cases isEmpty_or_nonempty κ with
  | inl hκ =>
      letI := hκ
      simp [klDivergence, marginal]
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
      have hJointFactorP (i : ι) (j : κ) :
          marginal p i * conditional p i j = p (i, j) := by
        simp only [conditional]
        field_simp [ne_of_gt (hMarginalPPos i)]
      have hConditionalSumP (i : ι) : ∑ j, conditional p i j = 1 := by
        simp only [conditional]
        rw [← Finset.sum_div, ← marginal]
        exact div_self (ne_of_gt (hMarginalPPos i))
      have hChainRatio (i : ι) (j : κ) :
          p (i, j) / q (i, j) =
            marginal p i / marginal q i *
              (conditional p i j / conditional q i j) := by
        simp only [conditional]
        field_simp [ne_of_gt (hq (i, j)), ne_of_gt (hMarginalPPos i),
          ne_of_gt (hMarginalQPos i)]
      simp only [klDivergence, Fintype.sum_prod_type]
      calc
        (∑ i, ∑ j, p (i, j) * Real.log (p (i, j) / q (i, j))) =
            ∑ i, ∑ j,
              (p (i, j) * Real.log (marginal p i / marginal q i) +
                p (i, j) *
                  Real.log (conditional p i j / conditional q i j)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [hChainRatio, Real.log_mul
            (ne_of_gt (div_pos (hMarginalPPos i) (hMarginalQPos i)))
            (ne_of_gt (div_pos (hConditionalPPos i j) (hConditionalQPos i j)))]
          ring
        _ = ∑ i,
              ((∑ j, p (i, j) * Real.log (marginal p i / marginal q i)) +
                ∑ j, p (i, j) *
                  Real.log (conditional p i j / conditional q i j)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_add_distrib]
        _ = ∑ i,
              (marginal p i * Real.log (marginal p i / marginal q i) +
                marginal p i * ∑ j, conditional p i j *
                  Real.log (conditional p i j / conditional q i j)) := by
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          · calc
              (∑ j, p (i, j) * Real.log (marginal p i / marginal q i)) =
                  ∑ j, (marginal p i * conditional p i j) *
                    Real.log (marginal p i / marginal q i) := by
                apply Finset.sum_congr rfl
                intro j _
                rw [hJointFactorP]
              _ = marginal p i * Real.log (marginal p i / marginal q i) *
                    ∑ j, conditional p i j := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                ring
              _ = marginal p i * Real.log (marginal p i / marginal q i) := by
                rw [hConditionalSumP, mul_one]
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [← hJointFactorP]
            ring
        _ = (∑ i, marginal p i * Real.log (marginal p i / marginal q i)) +
              ∑ i, marginal p i * ∑ j, conditional p i j *
                Real.log (conditional p i j / conditional q i j) := by
          rw [Finset.sum_add_distrib]

end D5.S3.Divergence.ChainRule

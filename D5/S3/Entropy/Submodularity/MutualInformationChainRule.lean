/- GID: D5/S3/Entropy/Submodularity/MutualInformationChainRule
   generality: G
   mirror-B: D5/B/S3/Entropy/Submodularity/MutualInformationChainRule
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove mutual-information chain rules and characterize DPI equality. -/

import D5.S3.Entropy.Submodularity.MarkovDataProcessing
import D5.S3.Entropy.MutualInformationSymm

/-!
# Mutual-information chain rule

This module proves the un-subtracted mutual-information chain rule, its monotonicity and equality
cases, and the equality converse for Markov data processing. It locally restates the six private
`MarkovDataProcessing` facts `yPivot`, `zPivot`, `entropy_yFirstLaw`, `marg_yFirstLaw`, `marg_xy`,
and `yFirstLaw_is_law` as `yPivot'`, `zPivot'`, `ent_yFirst`, `marg_yFirst`, `marg_xyProj`, and
`yFirst_is_law`. The append-only freeze law makes changing the frozen upstream module to export
private implementation facts unlawful, so private downstream restatement is the lawful extension.
The remaining local projection identities and `zFirst_is_law` are new private supporting facts.
-/

namespace D5.S3.Entropy.Submodularity.MutualInformationChainRule

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationEntropy
open D5.S3.Entropy.MutualInformationSymm
open D5.S3.Entropy.Submodularity.StrongSubadditivity
open D5.S3.Entropy.Submodularity.ConditionalMutualInformation
open D5.S3.Entropy.Submodularity.MarkovDataProcessing

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

private def yPivot' (ι κ μ : Type*) : κ × (ι × μ) ≃ ι × (κ × μ) where
  toFun q := (q.2.1, (q.1, q.2.2))
  invFun q := (q.2.1, (q.1, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private def zPivot' (ι κ μ : Type*) : μ × (ι × κ) ≃ ι × (κ × μ) where
  toFun q := (q.2.1, (q.2.2, q.1))
  invFun q := (q.2.2, (q.1, q.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

private theorem ent_yFirst (p : ι × (κ × μ) → ℝ) :
    shannonEntropy (yFirstLaw p) = shannonEntropy p :=
  Fintype.sum_equiv (yPivot' ι κ μ) _ _ (fun _ => rfl)

omit [Fintype ι] [Fintype κ] in
private theorem xy_yFirst (p : ι × (κ × μ) → ℝ) :
    xyProjection (yFirstLaw p) = fun r : κ × ι => xyProjection p (r.2, r.1) := by
  funext q
  simp only [xyProjection, yFirstLaw]

omit [Fintype κ] [Fintype μ] in
private theorem xz_yFirst (p : ι × (κ × μ) → ℝ) :
    xzProjection (yFirstLaw p) = marginal (fun s : (κ × μ) × ι => p (s.2, s.1)) := by
  funext q
  simp only [xzProjection, yFirstLaw, marginal]

omit [Fintype κ] in
private theorem marg_yFirst (p : ι × (κ × μ) → ℝ) :
    marginal (yFirstLaw p) = marginal (fun r : κ × ι => xyProjection p (r.2, r.1)) := by
  funext y
  simp only [marginal, yFirstLaw, xyProjection, Fintype.sum_prod_type]

omit [Fintype ι] in
private theorem marg_xyProj (p : ι × (κ × μ) → ℝ) :
    marginal (xyProjection p) = marginal p := by
  funext i
  simp only [marginal, xyProjection, Fintype.sum_prod_type]

private theorem yFirst_is_law (p : ι × (κ × μ) → ℝ)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    (∀ q, 0 ≤ yFirstLaw p q) ∧ ∑ q, yFirstLaw p q = 1 :=
  ⟨fun q => hp.1 _, by
    rw [← hp.2]; exact Fintype.sum_equiv (yPivot' ι κ μ) _ _ (fun _ => rfl)⟩

private theorem zFirst_is_law (p : ι × (κ × μ) → ℝ)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    (∀ q, 0 ≤ zFirstLaw p q) ∧ ∑ q, zFirstLaw p q = 1 :=
  ⟨fun q => hp.1 _, by
    rw [← hp.2]; exact Fintype.sum_equiv (zPivot' ι κ μ) _ _ (fun _ => rfl)⟩

/-- **Chain rule for mutual information.** -/
theorem mutual_information_chain_rule (p : ι × (κ × μ) → ℝ) (hp : ∀ x, 0 ≤ p x) :
    mutualInformation p =
      mutualInformation (xyProjection p) + conditionalMutualInformation (yFirstLaw p) := by
  classical
  have hxy_nonneg : ∀ q, 0 ≤ xyProjection p q := fun q =>
    Finset.sum_nonneg fun z _ => hp (q.1, (q.2, z))
  rw [mutual_information_eq_entropy_sub p hp,
    mutual_information_eq_entropy_sub (xyProjection p) hxy_nonneg,
    conditional_mutual_information_eq_entropy_defect (yFirstLaw p) (fun q => hp _),
    xy_yFirst, xz_yFirst, ent_yFirst, marg_yFirst, marg_xyProj,
    entropy_swap (xyProjection p)]
  ring

/-- Adjoining a second observation never decreases mutual information. -/
theorem mutual_information_le_pair (p : ι × (κ × μ) → ℝ)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    mutualInformation (xyProjection p) ≤ mutualInformation p := by
  have hchain := mutual_information_chain_rule p hp.1
  have hcmi := conditional_mutual_information_nonneg (yFirstLaw p) (yFirst_is_law p hp)
  linarith

/-- The extra observation is worthless exactly on conditionally factorizing slices. -/
theorem mutual_information_pair_eq_iff_conditional_product (p : ι × (κ × μ) → ℝ)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    mutualInformation p = mutualInformation (xyProjection p) ↔
      ∀ y, marginal (yFirstLaw p) y ≠ 0 →
        conditional (yFirstLaw p) y = fun q : ι × μ =>
          marginal (conditional (yFirstLaw p) y) q.1 *
            marginal (fun r : μ × ι => conditional (yFirstLaw p) y (r.2, r.1)) q.2 := by
  rw [← conditional_mutual_information_eq_zero_iff_conditional_product
    (yFirstLaw p) (yFirst_is_law p hp)]
  have hchain := mutual_information_chain_rule p hp.1
  constructor <;> intro h <;> linarith

/-- **Equality case of the data-processing inequality.** -/
theorem mutual_information_eq_of_markov_iff_conditional_product (p : ι × (κ × μ) → ℝ)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1)
    (hmarkov : ∀ x y z, p (x, (y, z)) * marginal (yFirstLaw p) y =
      xyProjection p (x, y) * xzProjection (yFirstLaw p) (y, z)) :
    mutualInformation (xzProjection p) = mutualInformation (xyProjection p) ↔
      ∀ z, marginal (zFirstLaw p) z ≠ 0 →
        conditional (zFirstLaw p) z = fun q : ι × κ =>
          marginal (conditional (zFirstLaw p) z) q.1 *
            marginal (fun r : κ × ι => conditional (zFirstLaw p) z (r.2, r.1)) q.2 := by
  rw [← conditional_mutual_information_eq_zero_iff_conditional_product
    (zFirstLaw p) (zFirst_is_law p hp)]
  have hgap := mutual_information_gap_eq_conditional_gap p hp.1
  rw [conditional_mutual_information_eq_zero_of_markov p hp hmarkov] at hgap
  constructor <;> intro h <;> linarith

end D5.S3.Entropy.Submodularity.MutualInformationChainRule

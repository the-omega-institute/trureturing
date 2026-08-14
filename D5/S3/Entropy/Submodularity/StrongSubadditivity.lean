/- GID: D5/S3/Entropy/Submodularity/StrongSubadditivity
   generality: G
   mirror-B: D5/B/S3/Entropy/Submodularity/StrongSubadditivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove strong subadditivity and characterize equality by conditional products. -/

/- Library-search audit trail (2026-08-15):
   * Repository and pinned-mathlib searches covered strong subadditivity, entropy submodularity,
     conditional mutual information, and conditional independence. No matching finite-real theorem
     was found; mathlib's conditional-independence API is measure-theoretic.
   * The proof composes the repository's entropy chain rule, two-variable entropy subadditivity,
     mutual-information entropy balance, and zero-mutual-information product characterization.
   * Right-nested products are retained so `conditionalEntropy p` is literally H(YZ|X).
-/

import D5.S3.Entropy.ConditionalEntropy
import D5.S3.Entropy.MutualInformationEntropy
import D5.S3.Entropy.MutualInformationIndependence

namespace D5.S3.Entropy.Submodularity.StrongSubadditivity

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationEntropy
open D5.S3.Entropy.MutualInformationIndependence

/-- The `(X,Y)` projection of a right-nested three-variable mass function. -/
noncomputable def xyProjection {ι κ μ : Type*} [Fintype μ]
    (p : ι × (κ × μ) → ℝ) (q : ι × κ) : ℝ :=
  ∑ z, p (q.1, (q.2, z))

/-- The `(X,Z)` projection of a right-nested three-variable mass function. -/
noncomputable def xzProjection {ι κ μ : Type*} [Fintype κ]
    (p : ι × (κ × μ) → ℝ) (q : ι × μ) : ℝ :=
  ∑ y, p (q.1, (y, q.2))

private theorem xyProjection_marginal_eq {ι κ μ : Type*} [Fintype κ] [Fintype μ]
    (p : ι × (κ × μ) → ℝ) : marginal (xyProjection p) = marginal p := by
  classical
  funext i
  simp only [marginal, xyProjection, Fintype.sum_prod_type]

private theorem xzProjection_marginal_eq {ι κ μ : Type*} [Fintype κ] [Fintype μ]
    (p : ι × (κ × μ) → ℝ) : marginal (xzProjection p) = marginal p := by
  classical
  funext i
  simp only [marginal, xzProjection, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

private theorem xyProjection_conditional_eq {ι κ μ : Type*} [Fintype κ] [Fintype μ]
    (p : ι × (κ × μ) → ℝ) (i : ι) :
    conditional (xyProjection p) i = marginal (conditional p i) := by
  classical
  funext y
  change (∑ z, p (i, (y, z))) / marginal (xyProjection p) i =
    ∑ z, p (i, (y, z)) / marginal p i
  rw [xyProjection_marginal_eq, Finset.sum_div]

private theorem xzProjection_conditional_eq {ι κ μ : Type*} [Fintype κ] [Fintype μ]
    (p : ι × (κ × μ) → ℝ) (i : ι) :
    conditional (xzProjection p) i =
      marginal (fun q : μ × κ => conditional p i (q.2, q.1)) := by
  classical
  funext z
  change (∑ y, p (i, (y, z))) / marginal (xzProjection p) i =
    ∑ y, p (i, (y, z)) / marginal p i
  rw [xzProjection_marginal_eq, Finset.sum_div]

private theorem marginal_nonneg {α β : Type*} [Fintype β] (p : α × β → ℝ)
    (hp : ∀ x, 0 ≤ p x) (a : α) : 0 ≤ marginal p a := by
  rw [marginal]
  exact Finset.sum_nonneg fun b _ => hp (a, b)

private theorem conditional_is_law {ι κ μ : Type*} [Fintype κ] [Fintype μ]
    (p : ι × (κ × μ) → ℝ) (hp : ∀ x, 0 ≤ p x) (i : ι)
    (hi : marginal p i ≠ 0) :
    (∀ q, 0 ≤ conditional p i q) ∧ ∑ q, conditional p i q = 1 := by
  constructor
  · intro q
    exact div_nonneg (hp (i, q)) (marginal_nonneg p hp i)
  · simp only [conditional]
    rw [← Finset.sum_div, ← marginal]
    exact div_self hi

/-- Conditional entropy is subadditive across the two coordinates conditioned on `X`. -/
theorem conditionalEntropy_pair_le_add {ι κ μ : Type*} [Fintype ι] [Fintype κ]
    [Fintype μ] (p : ι × (κ × μ) → ℝ)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    conditionalEntropy p ≤
      conditionalEntropy (xyProjection p) + conditionalEntropy (xzProjection p) := by
  classical
  have hslice (i : ι) :
      marginal p i * shannonEntropy (conditional p i) ≤
        marginal p i * shannonEntropy (marginal (conditional p i)) +
          marginal p i * shannonEntropy
            (marginal (fun q : μ × κ => conditional p i (q.2, q.1))) := by
    by_cases hi : marginal p i = 0
    · simp [hi]
    · calc
        marginal p i * shannonEntropy (conditional p i) ≤
            marginal p i *
              (shannonEntropy (marginal (conditional p i)) +
                shannonEntropy
                  (marginal (fun q : μ × κ => conditional p i (q.2, q.1)))) :=
          mul_le_mul_of_nonneg_left
            (entropy_subadditive (conditional p i) (conditional_is_law p hp.1 i hi))
            (marginal_nonneg p hp.1 i)
        _ = marginal p i * shannonEntropy (marginal (conditional p i)) +
              marginal p i * shannonEntropy
                (marginal (fun q : μ × κ => conditional p i (q.2, q.1))) := by ring
  rw [conditionalEntropy, conditionalEntropy, conditionalEntropy,
    xyProjection_marginal_eq, xzProjection_marginal_eq]
  simp_rw [xyProjection_conditional_eq, xzProjection_conditional_eq]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => hslice i

private theorem conditionalEntropy_gap_eq_sum_mutualInformation
    {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (p : ι × (κ × μ) → ℝ) (hp : ∀ x, 0 ≤ p x) :
    conditionalEntropy (xyProjection p) + conditionalEntropy (xzProjection p) -
        conditionalEntropy p =
      ∑ i, marginal p i * mutualInformation (conditional p i) := by
  classical
  rw [conditionalEntropy, conditionalEntropy, conditionalEntropy,
    xyProjection_marginal_eq, xzProjection_marginal_eq]
  simp_rw [xyProjection_conditional_eq, xzProjection_conditional_eq]
  calc
    (∑ i, marginal p i * shannonEntropy (marginal (conditional p i))) +
          (∑ i, marginal p i * shannonEntropy
            (marginal (fun q : μ × κ => conditional p i (q.2, q.1)))) -
        ∑ i, marginal p i * shannonEntropy (conditional p i) =
      ∑ i, marginal p i *
        (shannonEntropy (marginal (conditional p i)) +
          shannonEntropy
            (marginal (fun q : μ × κ => conditional p i (q.2, q.1))) -
          shannonEntropy (conditional p i)) := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = ∑ i, marginal p i * mutualInformation (conditional p i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mutual_information_eq_entropy_sub]
      intro q
      exact div_nonneg (hp (i, q)) (marginal_nonneg p hp i)

private theorem conditionalEntropy_pair_eq_iff_product
    {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (p : ι × (κ × μ) → ℝ) (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    conditionalEntropy p =
        conditionalEntropy (xyProjection p) + conditionalEntropy (xzProjection p) ↔
      ∀ i, marginal p i ≠ 0 →
        conditional p i = fun q : κ × μ =>
          marginal (conditional p i) q.1 *
            marginal (fun r : μ × κ => conditional p i (r.2, r.1)) q.2 := by
  classical
  have hgap := conditionalEntropy_gap_eq_sum_mutualInformation p hp.1
  have hsummand_nonneg (i : ι) :
      0 ≤ marginal p i * mutualInformation (conditional p i) := by
    by_cases hi : marginal p i = 0
    · simp [hi]
    · exact mul_nonneg (marginal_nonneg p hp.1 i)
        (mutual_information_nonneg (conditional p i) (conditional_is_law p hp.1 i hi))
  constructor
  · intro heq i hi
    have hsum : ∑ a, marginal p a * mutualInformation (conditional p a) = 0 := by
      rw [← hgap]
      linarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      fun a _ => hsummand_nonneg a).mp hsum
    have hmutual : mutualInformation (conditional p i) = 0 :=
      (mul_eq_zero.mp (hall i (Finset.mem_univ i))).resolve_left hi
    exact (mutual_information_eq_zero_iff_product
      (conditional p i) (conditional_is_law p hp.1 i hi)).1 hmutual
  · intro hproduct
    have hsum : ∑ i, marginal p i * mutualInformation (conditional p i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : marginal p i = 0
      · simp [hi]
      · rw [(mutual_information_eq_zero_iff_product
          (conditional p i) (conditional_is_law p hp.1 i hi)).2 (hproduct i hi), mul_zero]
    rw [← hgap] at hsum
    linarith

/-- Strong subadditivity in submodular form for a right-nested three-variable law. -/
theorem entropy_submodular {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (p : ι × (κ × μ) → ℝ) (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    shannonEntropy p + shannonEntropy (marginal p) ≤
      shannonEntropy (xyProjection p) + shannonEntropy (xzProjection p) := by
  rw [entropy_chain_rule p hp.1, entropy_chain_rule (xyProjection p),
    entropy_chain_rule (xzProjection p), xyProjection_marginal_eq, xzProjection_marginal_eq]
  · linarith [conditionalEntropy_pair_le_add p hp]
  · intro q
    exact Finset.sum_nonneg fun y _ => hp.1 (q.1, (y, q.2))
  · intro q
    exact Finset.sum_nonneg fun z _ => hp.1 (q.1, (q.2, z))

/-- Equality in strong subadditivity is conditional product factorization on every active slice. -/
theorem entropy_submodular_eq_iff_conditional_product
    {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (p : ι × (κ × μ) → ℝ) (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    shannonEntropy p + shannonEntropy (marginal p) =
        shannonEntropy (xyProjection p) + shannonEntropy (xzProjection p) ↔
      ∀ i, marginal p i ≠ 0 →
        conditional p i = fun q : κ × μ =>
          marginal (conditional p i) q.1 *
            marginal (fun r : μ × κ => conditional p i (r.2, r.1)) q.2 := by
  rw [entropy_chain_rule p hp.1, entropy_chain_rule (xyProjection p),
    entropy_chain_rule (xzProjection p), xyProjection_marginal_eq, xzProjection_marginal_eq]
  · constructor
    · intro h
      apply (conditionalEntropy_pair_eq_iff_product p hp).1
      linarith
    · intro h
      have := (conditionalEntropy_pair_eq_iff_product p hp).2 h
      linarith
  · intro q
    exact Finset.sum_nonneg fun y _ => hp.1 (q.1, (y, q.2))
  · intro q
    exact Finset.sum_nonneg fun z _ => hp.1 (q.1, (q.2, z))

end D5.S3.Entropy.Submodularity.StrongSubadditivity

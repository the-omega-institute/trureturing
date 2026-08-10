/- GID: D5/S3/Entropy/ConditionalEntropyEquality
   generality: G
   mirror-B: D5/B/S3/Entropy/ConditionalEntropyEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize vanishing conditional entropy on every positive-mass slice. -/

/- Library-search audit trail (2026-08-10):
   * Local pinned-mathlib grep terms: `conditionalEntropy`, `conditional_entropy`,
     `condEntropy`, entropy/conditional in both orders, `entropy_eq_zero`, and entropy next to
     point-mass names. The only zero characterization found was `Real.binEntropy_eq_zero` for
     the different scalar binary entropy; no finite-real conditional-entropy definition or
     vanishing characterization was found.
   * Repository-wide declaration and proposition grep covered every declaration in
     `D5/S3/Entropy` and `D5/S3/Divergence`, conditional entropy equal to zero in both orders,
     conditional laws next to point masses/Dirac laws, and functional-dependence wording.
     No duplicate or rearranged characterization was found.
   * The statement deliberately quantifies only over slices with nonzero first marginal.
     It says that the conditional law is a point mass on each such slice. It says nothing about
     zero-mass slices, where `conditional` is the artificial `0 / 0` law, and it does not claim
     a global second-coordinate function there.
-/

import D5.S3.Entropy.EntropyEquality
import D5.S3.Entropy.EntropyNonneg

namespace D5.S3.Entropy.ConditionalEntropyEquality

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.EntropyEquality
open D5.S3.Entropy.EntropyNonneg
open D5.S3.Entropy.MaxEntropy

open Classical in
/-- Point-mass conditionals on all nonzero-marginal slices force conditional entropy to vanish. -/
theorem conditional_entropy_eq_zero_of_point_mass_on_support
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ)
    (hpoint : ∀ i, marginal p i ≠ 0 →
      ∃ j, conditional p i = fun k => if k = j then 1 else 0) :
    conditionalEntropy p = 0 := by
  classical
  rw [conditionalEntropy]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hmarginal : marginal p i = 0
  · simp [hmarginal]
  · rcases hpoint i hmarginal with ⟨j, hpoint_mass⟩
    have hconditional_law :
        (∀ k, 0 ≤ conditional p i k) ∧ ∑ k, conditional p i k = 1 := by
      rw [hpoint_mass]
      constructor
      · intro k
        by_cases hkj : k = j <;> simp [hkj]
      · simp
    have hconditional_zero : shannonEntropy (conditional p i) = 0 :=
      (entropy_eq_zero_iff_point_mass (conditional p i) hconditional_law).2
        ⟨j, hpoint_mass⟩
    rw [hconditional_zero, mul_zero]

open Classical in
/-- Vanishing conditional entropy forces every nonzero-marginal conditional to be a point mass. -/
theorem point_mass_on_support_of_conditional_entropy_eq_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hentropy : conditionalEntropy p = 0) :
    ∀ i, marginal p i ≠ 0 →
      ∃ j, conditional p i = fun k => if k = j then 1 else 0 := by
  classical
  have hmarginal_nonneg (i : ι) : 0 ≤ marginal p i := by
    rw [marginal]
    exact Finset.sum_nonneg fun j _ => hp (i, j)
  have hconditional_law (i : ι) (hmarginal : marginal p i ≠ 0) :
      (∀ j, 0 ≤ conditional p i j) ∧ ∑ j, conditional p i j = 1 := by
    constructor
    · intro j
      exact div_nonneg (hp (i, j)) (hmarginal_nonneg i)
    · simp only [conditional]
      rw [← Finset.sum_div, ← marginal]
      exact div_self hmarginal
  have hsummand_nonneg (i : ι) :
      0 ≤ marginal p i * shannonEntropy (conditional p i) := by
    by_cases hmarginal : marginal p i = 0
    · simp [hmarginal]
    · exact mul_nonneg (hmarginal_nonneg i)
        (shannon_entropy_nonneg (conditional p i) (hconditional_law i hmarginal))
  rw [conditionalEntropy] at hentropy
  have hall_summands :
      ∀ i ∈ Finset.univ, marginal p i * shannonEntropy (conditional p i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hsummand_nonneg i).mp hentropy
  intro i hmarginal
  have hsummand_zero :
      marginal p i * shannonEntropy (conditional p i) = 0 :=
    hall_summands i (Finset.mem_univ i)
  have hconditional_zero : shannonEntropy (conditional p i) = 0 :=
    (mul_eq_zero.mp hsummand_zero).resolve_left hmarginal
  exact (entropy_eq_zero_iff_point_mass
    (conditional p i) (hconditional_law i hmarginal)).1 hconditional_zero

open Classical in
/-- Conditional entropy vanishes exactly when every nonzero-marginal conditional is a point mass. -/
theorem conditional_entropy_eq_zero_iff_point_mass_on_support
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (hp : ∀ x, 0 ≤ p x) :
    conditionalEntropy p = 0 ↔
      ∀ i, marginal p i ≠ 0 →
        ∃ j, conditional p i = fun k => if k = j then 1 else 0 := by
  constructor
  · exact point_mass_on_support_of_conditional_entropy_eq_zero p hp
  · exact conditional_entropy_eq_zero_of_point_mass_on_support p

end D5.S3.Entropy.ConditionalEntropyEquality

/- GID: D5/S3/Entropy/Mixing/MixtureEntropyUpperEquality
   generality: G
   mirror-B: D5/B/S3/Entropy/Mixing/MixtureEntropyUpperEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Upper mixture-entropy equality is equivalent to disjoint active component supports. -/

/- Library-search audit trail (2026-08-15):
   * Repository search covered mixture-entropy equality names, pairwise-disjoint supports, and
     uses of the conditional-entropy zero characterization. No duplicate theorem was found.
   * The frozen mixture bracket supplies the selector-output joint law and both marginal and
     chain-rule identities. The frozen conditional-entropy equality theorem supplies the exact
     point-mass-on-positive-slices engine required for the upper endpoint.
   * Pinned-mathlib search found the standard `Set.PairwiseDisjoint` support API, including its
     pointwise disjointness eliminators. The proof uses those declarations for the finite support
     equivalence rather than introducing a second disjointness notion.
-/

import D5.S3.Entropy.ConditionalEntropyEquality
import D5.S3.Entropy.Mixing.MixtureEntropyBracket

namespace D5.S3.Entropy.Mixing.MixtureEntropyUpperEquality

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.ConditionalEntropyEquality
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.Mixing.MixtureEntropyBracket
open D5.S3.Entropy.MutualInformationSymm

open Classical in
private theorem point_mass_selector_iff_pairwise_disjoint_supports
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (q : ι → κ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hq : ∀ i j, 0 ≤ q i j) :
    (∀ j, marginal (fun z : κ × ι => mixtureJoint w q (z.2, z.1)) j ≠ 0 →
      ∃ i, conditional (fun z : κ × ι => mixtureJoint w q (z.2, z.1)) j =
        fun k => if k = i then 1 else 0) ↔
      (Function.support w).PairwiseDisjoint (fun i => Function.support (q i)) := by
  classical
  let p : κ × ι → ℝ := fun z => mixtureJoint w q (z.2, z.1)
  have hp : ∀ z, 0 ≤ p z := fun z => mul_nonneg (hw z.2) (hq z.2 z.1)
  constructor
  · intro hpoint i hi i' hi' hii'
    apply Set.disjoint_left.2
    intro j hji hji'
    have hwi_pos : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hi)
    have hqi_pos : 0 < q i j := lt_of_le_of_ne (hq i j) (Ne.symm hji)
    have hmarginal_pos : 0 < marginal p j := by
      rw [marginal]
      calc
        0 < p (j, i) := mul_pos hwi_pos hqi_pos
        _ ≤ ∑ k, p (j, k) :=
          Finset.single_le_sum (fun k _ => hp (j, k)) (Finset.mem_univ i)
    rcases hpoint j (ne_of_gt hmarginal_pos) with ⟨i₀, hconditional⟩
    have hconditional_ne (k : ι) (hwk : w k ≠ 0) (hqk : q k j ≠ 0) :
        conditional p j k ≠ 0 := by
      rw [conditional]
      exact div_ne_zero (mul_ne_zero hwk hqk) (ne_of_gt hmarginal_pos)
    have hi_eq : i = i₀ := by
      by_contra hne
      have heval := congrFun hconditional i
      rw [if_neg hne] at heval
      exact hconditional_ne i hi hji heval
    have hi'_eq : i' = i₀ := by
      by_contra hne
      have heval := congrFun hconditional i'
      rw [if_neg hne] at heval
      exact hconditional_ne i' hi' hji' heval
    exact hii' (hi_eq.trans hi'_eq.symm)
  · intro hdisjoint j hmarginal_ne
    have hexists : ∃ i, w i * q i j ≠ 0 := by
      by_contra h
      push Not at h
      apply hmarginal_ne
      rw [marginal]
      exact Finset.sum_eq_zero fun i _ => h i
    rcases hexists with ⟨i₀, hcell⟩
    have hwi₀ : w i₀ ≠ 0 := left_ne_zero_of_mul hcell
    have hqi₀ : q i₀ j ≠ 0 := right_ne_zero_of_mul hcell
    have hother (i : ι) (hi : i ≠ i₀) : w i * q i j = 0 := by
      by_cases hwi : w i = 0
      · simp [hwi]
      by_cases hqi : q i j = 0
      · simp [hqi]
      exact False.elim
        (Set.disjoint_left.1 (hdisjoint hwi hwi₀ hi) hqi hqi₀)
    have hmarginal_eq : marginal p j = w i₀ * q i₀ j := by
      rw [marginal, Finset.sum_eq_single i₀]
      · rfl
      · intro i _ hi
        exact hother i hi
      · simp
    refine ⟨i₀, ?_⟩
    funext i
    rw [conditional, hmarginal_eq]
    by_cases hi : i = i₀
    · subst i
      simp [mixtureJoint, hcell]
    · simp [mixtureJoint, hother i hi, hi]

/-- The upper mixture-entropy bound is sharp exactly when the positive-weight components have
pairwise disjoint supports. Zero-weight components impose no support restriction. -/
theorem mixture_entropy_eq_weighted_add_weight_entropy_iff_pairwise_disjoint_supports
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (q : ι → κ → ℝ)
    (hw : (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1)
    (hq : ∀ i, (∀ j, 0 ≤ q i j) ∧ ∑ j, q i j = 1) :
    shannonEntropy (mixture w q) =
        shannonEntropy w + ∑ i, w i * shannonEntropy (q i) ↔
      (Function.support w).PairwiseDisjoint (fun i => Function.support (q i)) := by
  have hjoint_nonneg : ∀ z, 0 ≤ mixtureJoint w q z :=
    fun z => mul_nonneg (hw.1 z.1) ((hq z.1).1 z.2)
  have hswap_nonneg :
      ∀ z : κ × ι, 0 ≤ mixtureJoint w q (z.2, z.1) :=
    fun z => hjoint_nonneg (z.2, z.1)
  have hchain := entropy_chain_rule (mixtureJoint w q) hjoint_nonneg
  have hswap_chain := entropy_chain_rule
    (fun z : κ × ι => mixtureJoint w q (z.2, z.1)) hswap_nonneg
  rw [mixtureJoint_marginal_eq_weight w q fun i => (hq i).2,
    mixtureJoint_conditionalEntropy_eq_weighted w q fun i => (hq i).2] at hchain
  rw [entropy_swap, mixtureJoint_swapped_marginal_eq_mixture w q] at hswap_chain
  have hzero :
      shannonEntropy (mixture w q) =
          shannonEntropy w + ∑ i, w i * shannonEntropy (q i) ↔
        conditionalEntropy (fun z : κ × ι => mixtureJoint w q (z.2, z.1)) = 0 := by
    constructor <;> intro h <;> linarith
  rw [hzero, conditional_entropy_eq_zero_iff_point_mass_on_support _ hswap_nonneg]
  exact point_mass_selector_iff_pairwise_disjoint_supports w q hw.1 fun i => (hq i).1

end D5.S3.Entropy.Mixing.MixtureEntropyUpperEquality

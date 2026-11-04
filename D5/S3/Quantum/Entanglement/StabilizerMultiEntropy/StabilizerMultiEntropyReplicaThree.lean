/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/StabilizerMultiEntropyReplicaThree
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/StabilizerMultiEntropyReplicaThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two- and three-party reduction, vanishing criterion, and determination of replica-three multi-entropies. -/

import D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse

/-!
# Reduction, vanishing criterion, and coarse determination of replica-three stabilizer multi-entropy
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.StabilizerMultiEntropyReplicaThree

open scoped BigOperators
open D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
open D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence

private lemma zpow_two_sub_eq_inv_pow {k : ℕ} (hk : 2 ≤ k) :
    (3 : ℝ) ^ (2 - (k : ℤ)) = ((3 : ℝ) ^ (k - 2))⁻¹ := by
  have hexp : (2 - (k : ℤ)) = -(((k - 2 : ℕ) : ℤ)) := by omega
  rw [hexp, zpow_neg, zpow_natCast]

private lemma coarseMultiEntropy_eq_zpow_upperRankSum {N q : ℕ}
    (Γ : Matrix (Fin N) (Fin N) (ZMod 2)) (ψ : (Fin N → Fin 2) → ℂ)
    (hΓψ : IsGraphFormOf Γ ψ) (col : Fin N → Fin q)
    {ρ : PartyPartition q} (hρ : 2 ≤ ρ.parts.card) :
    coarseMultiEntropy ρ col ψ =
      (Real.log 2 / 2) * ((3 : ℝ) ^ (2 - (ρ.parts.card : ℤ)) *
        upperRankSum (fun τ ↦ (partitionRank Γ col τ : ℝ)) ρ) := by
  have hform := (party_symmetry_coarse_graining_and_bipartite_entropy.2.1
    Γ ψ hΓψ col ρ hρ ρ.parts.equivFin.symm).2
  rw [hform, zpow_two_sub_eq_inv_pow hρ]
  unfold upperRankSum
  ring

/-- For `q ≥ 3`, the `q`-party replica-three stabilizer multi-entropy is an explicit linear
combination of the three-party and two-party coarse-grained replica-three multi-entropies. -/
theorem replica_three_two_and_three_party_reduction
    {N q : ℕ} (hq : 3 ≤ q) (ψ : (Fin N → Fin 2) → ℂ)
    (hstab : StabilizedBy pauliSet ψ) (hnorm : (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1)
    (col : Fin N → Fin q) :
    S 3 q col ψ = (3 : ℝ) ^ (2 - (q : ℤ)) *
      (∑ π ∈ partitionsOfCard q 3, 3 * coarseMultiEntropy π col ψ +
       ∑ σ ∈ partitionsOfCard q 2,
         ((3 : ℝ) - ∑ B ∈ σ.parts, (2 : ℝ) ^ (B.card - 1)) * coarseMultiEntropy σ col ψ) := by
  obtain ⟨Γ, hΓψ⟩ := graph_form_existence_and_replica_rank_formula.2.1 ψ hstab hnorm
  let r : PartyPartition q → ℝ := fun τ ↦ (partitionRank Γ col τ : ℝ)
  have hq2 : 2 ≤ q := by omega
  have hS : S 3 q col ψ =
      (3 : ℝ) ^ (2 - (q : ℤ)) * ((Real.log 2 / 2) * ∑ σ ∈ twoOrThreePartitions q, r σ) := by
    rw [replica_three_coarse_partition_sum.2.2 hq2 Γ ψ hΓψ col, zpow_two_sub_eq_inv_pow hq2]
    dsimp [r]; ring
  have h3 : ∑ π ∈ partitionsOfCard q 3, 3 * coarseMultiEntropy π col ψ =
      (Real.log 2 / 2) * ∑ π ∈ partitionsOfCard q 3, upperRankSum r π := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun π hπ ↦ ?_
    have hcard : π.parts.card = 3 := (Finset.mem_filter.mp hπ).2
    rw [coarseMultiEntropy_eq_zpow_upperRankSum Γ ψ hΓψ col (by omega : 2 ≤ π.parts.card), hcard]
    dsimp [r]; norm_num; ring
  have h2 : ∑ σ ∈ partitionsOfCard q 2,
        ((3 : ℝ) - ∑ B ∈ σ.parts, (2 : ℝ) ^ (B.card - 1)) * coarseMultiEntropy σ col ψ =
      (Real.log 2 / 2) * ∑ σ ∈ partitionsOfCard q 2,
        ((3 : ℝ) - ∑ B ∈ σ.parts, (2 : ℝ) ^ (B.card - 1)) * upperRankSum r σ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ hσ ↦ ?_
    have hcard : σ.parts.card = 2 := (Finset.mem_filter.mp hσ).2
    rw [coarseMultiEntropy_eq_zpow_upperRankSum Γ ψ hΓψ col (by omega : 2 ≤ σ.parts.card), hcard]
    dsimp [r]; norm_num; ring
  rw [hS, h3, h2, ← mul_add, ← coarse_upper_sum_reduction_and_triangular_inversion.1 hq r]

/-- Linear combinations of coarse-grained replica-three stabilizer multi-entropies expand as
weighted sums of two- and three-block partition ranks on every graph form, and vanish across all
normalized pure qubit stabilizer states and colourings whenever all coarse weights vanish. -/
theorem coarse_linear_combination_and_vanishing_criterion
    {q : ℕ} (hq : 2 ≤ q) (c : PartyPartition q → ℝ) :
    (∀ {N : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2)) (ψ : (Fin N → Fin 2) → ℂ),
      IsGraphFormOf Γ ψ → ∀ (col : Fin N → Fin q),
        ∑ ρ ∈ nontrivialPartitions q, c ρ * coarseMultiEntropy ρ col ψ =
          (Real.log 2 / 2) *
            ∑ σ ∈ twoOrThreePartitions q, coarseWeight c σ * (partitionRank Γ col σ : ℝ)) ∧
    ((∀ σ ∈ twoOrThreePartitions q, coarseWeight c σ = 0) →
      ∀ {N : ℕ} (ψ : (Fin N → Fin 2) → ℂ),
        StabilizedBy pauliSet ψ → (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1 →
        ∀ (col : Fin N → Fin q),
          ∑ ρ ∈ nontrivialPartitions q, c ρ * coarseMultiEntropy ρ col ψ = 0) := by
  have _ : 2 ≤ q := hq
  have hexpand : ∀ {N : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2)) (ψ : (Fin N → Fin 2) → ℂ),
      IsGraphFormOf Γ ψ → ∀ (col : Fin N → Fin q),
        ∑ ρ ∈ nontrivialPartitions q, c ρ * coarseMultiEntropy ρ col ψ =
          (Real.log 2 / 2) *
            ∑ σ ∈ twoOrThreePartitions q, coarseWeight c σ * (partitionRank Γ col σ : ℝ) := by
    intro N Γ ψ hΓψ col
    let r : PartyPartition q → ℝ := fun τ ↦ (partitionRank Γ col τ : ℝ)
    calc ∑ ρ ∈ nontrivialPartitions q, c ρ * coarseMultiEntropy ρ col ψ
        = ∑ ρ ∈ nontrivialPartitions q,
            (Real.log 2 / 2) * (c ρ * ((3 : ℝ) ^ (2 - (ρ.parts.card : ℤ)) * upperRankSum r ρ)) :=
          Finset.sum_congr rfl fun ρ hρ ↦ by
            have hρ2 : 2 ≤ ρ.parts.card := (Finset.mem_filter.mp hρ).2
            rw [coarseMultiEntropy_eq_zpow_upperRankSum Γ ψ hΓψ col hρ2]
            dsimp [r]; ring
      _ = (Real.log 2 / 2) * ∑ ρ ∈ nontrivialPartitions q,
            c ρ * ((3 : ℝ) ^ (2 - (ρ.parts.card : ℤ)) * upperRankSum r ρ) := by
          rw [← Finset.mul_sum]
      _ = (Real.log 2 / 2) *
            ∑ σ ∈ twoOrThreePartitions q, coarseWeight c σ * (partitionRank Γ col σ : ℝ) := by
          rw [coarse_upper_sum_reduction_and_triangular_inversion.2.1 c r]
  refine ⟨hexpand, fun hzero N ψ hstab hnorm col ↦ ?_⟩
  obtain ⟨Γ, hΓψ⟩ := graph_form_existence_and_replica_rank_formula.2.1 ψ hstab hnorm
  rw [hexpand Γ ψ hΓψ col, Finset.sum_eq_zero (fun σ hσ ↦ by rw [hzero σ hσ, zero_mul]), mul_zero]

/-- Two normalized pure qubit stabilizer states, possibly on different numbers of qubits, with
matching two-party and three-party coarse replica-three multi-entropies agree on all coarse
replica-three multi-entropies with at least two blocks and on `S_3^{(q)}`. -/
theorem coarse_two_three_data_determine_replica_three_multi_entropies
    {N N' q : ℕ} (hq : 2 ≤ q)
    (ψ : (Fin N → Fin 2) → ℂ) (ψ' : (Fin N' → Fin 2) → ℂ)
    (hstab : StabilizedBy pauliSet ψ) (hnorm : (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1)
    (hstab' : StabilizedBy pauliSet ψ') (hnorm' : (∑ x : Fin N' → Fin 2, ‖ψ' x‖ ^ 2) = 1)
    (col : Fin N → Fin q) (col' : Fin N' → Fin q)
    (h2 : ∀ σ ∈ partitionsOfCard q 2,
      coarseMultiEntropy σ col ψ = coarseMultiEntropy σ col' ψ')
    (h3 : ∀ π ∈ partitionsOfCard q 3,
      coarseMultiEntropy π col ψ = coarseMultiEntropy π col' ψ') :
    (∀ ρ ∈ nontrivialPartitions q,
      coarseMultiEntropy ρ col ψ = coarseMultiEntropy ρ col' ψ') ∧
    S 3 q col ψ = S 3 q col' ψ' := by
  obtain ⟨Γ, hΓψ⟩ := graph_form_existence_and_replica_rank_formula.2.1 ψ hstab hnorm
  obtain ⟨Γ', hΓ'ψ'⟩ := graph_form_existence_and_replica_rank_formula.2.1 ψ' hstab' hnorm'
  let r₁ : PartyPartition q → ℝ := fun τ ↦ (partitionRank Γ col τ : ℝ)
  let r₂ : PartyPartition q → ℝ := fun τ ↦ (partitionRank Γ' col' τ : ℝ)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpref_ne : ∀ k : ℕ, (Real.log 2 / 2) * (3 : ℝ) ^ (2 - (k : ℤ)) ≠ 0 := fun k ↦
    mul_ne_zero (div_ne_zero hlog.ne' (by norm_num)) (zpow_ne_zero _ (by norm_num))
  have hcancel : ∀ {ρ : PartyPartition q}, 2 ≤ ρ.parts.card →
      coarseMultiEntropy ρ col ψ = coarseMultiEntropy ρ col' ψ' →
      upperRankSum r₁ ρ = upperRankSum r₂ ρ := fun {ρ} hρ2 heq ↦ by
    rw [coarseMultiEntropy_eq_zpow_upperRankSum Γ ψ hΓψ col hρ2,
      coarseMultiEntropy_eq_zpow_upperRankSum Γ' ψ' hΓ'ψ' col' hρ2,
      ← mul_assoc, ← mul_assoc] at heq
    exact mul_left_cancel₀ (hpref_ne ρ.parts.card) heq
  have hurs2 : ∀ σ ∈ partitionsOfCard q 2, upperRankSum r₁ σ = upperRankSum r₂ σ :=
    fun σ hσ ↦ hcancel (by have := (Finset.mem_filter.mp hσ).2; omega) (h2 σ hσ)
  have hurs3 : ∀ π ∈ partitionsOfCard q 3, upperRankSum r₁ π = upperRankSum r₂ π :=
    fun π hπ ↦ hcancel (by have := (Finset.mem_filter.mp hπ).2; omega) (h3 π hπ)
  have hall_urs := (coarse_upper_sum_reduction_and_triangular_inversion.2.2.2 r₁ r₂ hurs2 hurs3).2
  have hall_ent : ∀ ρ ∈ nontrivialPartitions q,
      coarseMultiEntropy ρ col ψ = coarseMultiEntropy ρ col' ψ' := fun ρ hρ ↦ by
    have hρ2 : 2 ≤ ρ.parts.card := (Finset.mem_filter.mp hρ).2
    rw [coarseMultiEntropy_eq_zpow_upperRankSum Γ ψ hΓψ col hρ2,
      coarseMultiEntropy_eq_zpow_upperRankSum Γ' ψ' hΓ'ψ' col' hρ2]
    dsimp [r₁, r₂] at hall_urs
    rw [hall_urs ρ]
  refine ⟨hall_ent, ?_⟩
  have hbot : (⊥ : PartyPartition q) ∈ nontrivialPartitions q := by
    simp [nontrivialPartitions, Finpartition.card_bot, hq]
  rw [← party_symmetry_coarse_graining_and_bipartite_entropy.2.2.1 hq ψ hstab hnorm col,
    ← party_symmetry_coarse_graining_and_bipartite_entropy.2.2.1 hq ψ' hstab' hnorm' col',
    hall_ent (⊥ : PartyPartition q) hbot]

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.StabilizerMultiEntropyReplicaThree

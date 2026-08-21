/- GID: D5/S3/Entropy/Fusion/StateEntropy
   generality: G
   mirror-B: D5/B/S3/Entropy/Fusion/StateEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fusion entropy equals joint entropy and both chain-rule forms. -/

import D5.S3.Entropy.Forgetting.CapacityMonotone
import D5.S3.Entropy.MutualInformationSymm
import D5.S3.Entropy.Relabeling.InjectiveInvariance

/- Library-search audit trail (2026-08-21):
   * Exact repository hits `pushforward`, `conditionalEntropy`, and
     `entropy_chain_rule` provide the source-semantic finite laws and both
     Shannon decompositions; all are applied below.
   * Exact repository hit `shannonEntropy_extend_injective` supplies entropy
     invariance under the injective joint embedding and is applied below.
   * Exact repository hit `entropy_swap` supplies the second-coordinate chain
     rule after swapping the joint law. No single declaration packages the
     source's fusion embedding and all three equalities.
   * Pinned Mathlib searches found only the finite-sum reindexing primitives
     already used by these repository declarations. Loogle found no stronger
     combined theorem; LeanSearch's endpoint returned HTTP 404. -/

namespace D5.S3.Entropy.Fusion.StateEntropy

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.MutualInformationSymm
open D5.S3.Entropy.Relabeling.InjectiveInvariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The fused state has the entropy of the jointly predicted pair, and the two
conditional entropies give the two Shannon chain-rule decompositions. -/
theorem fusion_state_entropy_identity
    {Y Z1 Z2 Z12 : Type*}
    [Fintype Y] [Fintype Z1] [Fintype Z2] [Fintype Z12]
    (mass : Y -> Real)
    (fusedState : Y -> Z12)
    (firstState : Y -> Z1)
    (secondState : Y -> Z2)
    (jointEmbedding : Z12 -> Z1 × Z2)
    (mass_nonnegative : forall y, 0 <= mass y)
    (fused_surjective : Function.Surjective fusedState)
    (joint_injective : Function.Injective jointEmbedding)
    (joint_realizes : forall y,
      jointEmbedding (fusedState y) = (firstState y, secondState y)) :
    shannonEntropy (pushforward fusedState mass) =
        shannonEntropy (pushforward (fun y => (firstState y, secondState y)) mass) /\
      shannonEntropy (pushforward fusedState mass) =
        shannonEntropy (pushforward firstState mass) +
          conditionalEntropy
            (pushforward (fun y => (firstState y, secondState y)) mass) /\
      shannonEntropy (pushforward fusedState mass) =
        shannonEntropy (pushforward secondState mass) +
          conditionalEntropy
            (fun pair : Z2 × Z1 =>
              pushforward (fun y => (firstState y, secondState y)) mass
                (pair.2, pair.1)) := by
  classical
  let pairMap : Y -> Z1 × Z2 := fun y => (firstState y, secondState y)
  let fusedLaw : Z12 -> Real := pushforward fusedState mass
  let pairLaw : Z1 × Z2 -> Real := pushforward pairMap mass
  let swappedLaw : Z2 × Z1 -> Real :=
    fun pair => pairLaw (pair.2, pair.1)
  have range_pair : Set.range pairMap = Set.range jointEmbedding := by
    apply Set.Subset.antisymm
    · rintro pair ⟨y, rfl⟩
      exact ⟨fusedState y, (joint_realizes y)⟩
    · rintro pair ⟨state, rfl⟩
      obtain ⟨y, hy⟩ := fused_surjective state
      refine ⟨y, ?_⟩
      calc
        pairMap y = jointEmbedding (fusedState y) := (joint_realizes y).symm
        _ = jointEmbedding state := congrArg jointEmbedding hy
  have pairLaw_extension :
      pairLaw = Function.extend jointEmbedding fusedLaw (fun _ => 0) := by
    funext pair
    by_cases hpair : pair ∈ Set.range jointEmbedding
    · rcases hpair with ⟨state, hstate⟩
      have hiff (y : Y) : pairMap y = pair <-> fusedState y = state := by
        constructor
        · intro h
          apply joint_injective
          calc
            jointEmbedding (fusedState y) = pairMap y := joint_realizes y
            _ = pair := h
            _ = jointEmbedding state := hstate.symm
        · intro h
          calc
            pairMap y = jointEmbedding (fusedState y) := (joint_realizes y).symm
            _ = jointEmbedding state := congrArg jointEmbedding h
            _ = pair := hstate
      have hsum : pairLaw pair = fusedLaw state := by
        simp only [pairLaw, fusedLaw, pushforward]
        apply Finset.sum_congr rfl
        intro y _
        simp only [hiff y]
      calc
        pairLaw pair = fusedLaw state := hsum
        _ = Function.extend jointEmbedding fusedLaw (fun _ => 0) pair := by
          rw [← hstate]
          exact (joint_injective.extend_apply fusedLaw (fun _ => 0) state).symm
    · have hpairMap : pair ∉ Set.range pairMap := by
        intro h
        apply hpair
        exact range_pair ▸ h
      have hpairMap' : ¬ exists y, pairMap y = pair := hpairMap
      have hjoint' : ¬ exists state, jointEmbedding state = pair := hpair
      simp only [pairLaw, pushforward]
      rw [Finset.sum_eq_zero]
      · rw [Function.extend_apply' _ _ _ hjoint']
      · intro y _
        have hnot : pairMap y ≠ pair := fun h => hpairMap' ⟨y, h⟩
        simp [hnot]
  have pairLaw_nonnegative : forall pair, 0 <= pairLaw pair := by
    intro pair
    simp only [pairLaw, pushforward]
    exact Finset.sum_nonneg fun y _ => by
      by_cases h : pairMap y = pair <;> simp [h, mass_nonnegative y]
  have marginal_first :
      marginal pairLaw = pushforward firstState mass := by
    funext firstValue
    simp only [marginal, pairLaw, pairMap, pushforward]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_eq_single (secondState y)]
    · by_cases h : firstState y = firstValue <;> simp [h]
    · intro other _ hother
      split_ifs with heq
      · exact (hother (congrArg Prod.snd heq).symm).elim
      · rfl
    · simp
  have marginal_second :
      marginal swappedLaw = pushforward secondState mass := by
    funext secondValue
    simp only [swappedLaw, marginal, pairLaw, pairMap, pushforward]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_eq_single (firstState y)]
    · by_cases h : secondState y = secondValue <;> simp [h]
    · intro other _ hother
      split_ifs with heq
      · exact (hother (congrArg Prod.fst heq).symm).elim
      · rfl
    · simp
  have first_chain := entropy_chain_rule pairLaw pairLaw_nonnegative
  rw [marginal_first] at first_chain
  have swapped_nonnegative : forall pair, 0 <= swappedLaw pair := by
    intro pair
    exact pairLaw_nonnegative (pair.2, pair.1)
  have second_chain := entropy_chain_rule swappedLaw swapped_nonnegative
  rw [marginal_second] at second_chain
  have fused_eq_pair :
      shannonEntropy fusedLaw = shannonEntropy pairLaw := by
    calc
      shannonEntropy fusedLaw =
          shannonEntropy (Function.extend jointEmbedding fusedLaw (fun _ => 0)) :=
        (shannonEntropy_extend_injective joint_injective fusedLaw).symm
      _ = shannonEntropy pairLaw := congrArg shannonEntropy pairLaw_extension.symm
  have pair_swap := entropy_swap pairLaw
  refine ⟨?_, ?_, ?_⟩
  · exact fused_eq_pair
  · calc
      shannonEntropy fusedLaw = shannonEntropy pairLaw := fused_eq_pair
      _ = shannonEntropy (pushforward firstState mass) +
          conditionalEntropy pairLaw := first_chain
  · calc
      shannonEntropy fusedLaw = shannonEntropy pairLaw := fused_eq_pair
      _ = shannonEntropy swappedLaw := pair_swap.symm
      _ = shannonEntropy (pushforward secondState mass) +
          conditionalEntropy swappedLaw := second_chain

#print axioms fusion_state_entropy_identity

end D5.S3.Entropy.Fusion.StateEntropy

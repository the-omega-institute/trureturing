/- GID: D5/S3/ObserverMemory/FunctionalGraphs/ActualTransferJordanChains
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FunctionalGraphs/ActualTransferJordanChains
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual transient Jordan chains realize the transfer rank-loss block profile. -/

import D5.S1.Eigenstructure.NilpotentJordanChains
import D5.S3.ObserverMemory.FunctionalGraphs.InformationLossJordanLayers

namespace D5.S3.ObserverMemory.FunctionalGraphs.ActualTransferJordanChains

open Module
open D5.S1.Eigenstructure.NilpotentJordanChains
open D5.S3.Estimation.ExperimentCost.KernelTowerNilpotentRecovery
open D5.S3.ObserverMemory.FunctionalGraphs.FiniteFunctionalGraphFittingDecomposition
open D5.S3.ObserverMemory.FunctionalGraphs.InformationLossJordanLayers
open D5.S3.ObserverMemory.InverseLimits.IdentityFuturePastGap
open D5.S3.ObserverMemory.InverseLimits.StableImagePeriodicCore
open D5.S3.ObserverMemory.InverseLimits.TraceRankCombinatorics
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private theorem chain_profile_kernel {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Fintype ι]
    (f : Module.End K V) (s : ι → ℕ+) (b : Basis (Σ i, Fin (s i)) K V)
    (hrank : ∀ m, Module.finrank K (LinearMap.range (f ^ m)) =
      ∑ i, ((s i : ℕ) - m)) (m : ℕ) :
    blockKernelTower (Finset.univ.val.map s) m =
      Module.finrank K (LinearMap.ker (f ^ m)) := by
  classical
  have hdim : Module.finrank K V = ∑ i, (s i : ℕ) := by
    simpa using Module.finrank_eq_card_basis b
  have hsum : (∑ i, ((s i : ℕ) - m)) + (∑ i, min m (s i : ℕ)) =
      ∑ i, (s i : ℕ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    omega
  have hnull := LinearMap.finrank_range_add_finrank_ker (f ^ m)
  rw [hrank, hdim] at hnull
  have heq : (∑ i, min m (s i : ℕ)) =
      Module.finrank K (LinearMap.ker (f ^ m)) := by omega
  change ((Finset.univ.val.map s).map (fun size : ℕ+ => min m size.val)).sum = _
  rw [Multiset.map_map]
  exact heq

private theorem profiles_eq {left right : BlockMultiset}
    (hdim : blockProfileDimension left = blockProfileDimension right)
    (htower : ∀ k, blockKernelTower left k = blockKernelTower right k) :
    left = right := by
  have h := finite_kernel_tower_recovers_block_profile
    (n := blockProfileDimension left) ⟨left, rfl⟩ ⟨right, hdim.symm⟩
    (fun k _ _ => htower k)
  exact congrArg Subtype.val h

/-- The finite-map loss theorem with actual Jordan chains on the transient
Fitting summand. The positive chain lengths realize the previously abstract
multiset, so both block counts in the conclusion count genuine chains. -/
theorem information_loss_layers_from_actual_jordan_chains
    {Y : Type*} [Finite Y] (tau : Y → Y) :
    ∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ+)
      (b : Basis (Σ i, Fin (s i)) ℂ (transientSubspace tau (Nat.card Y))),
      (∀ (m : ℕ) (i : ι) (j : Fin (s i)),
        (transientTransfer tau (Nat.card Y) ^ m) (b ⟨i, j⟩) =
          if h : j.val + m < s i then b ⟨i, ⟨j.val + m, h⟩⟩ else 0) ∧
      Finset.univ.val.map s = transferZeroBlocks tau ∧
      ∀ k : ℕ, 0 < k →
        (informationLossLayer tau k =
            Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k.pred)) -
              Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k)) ∧
          informationLossLayer tau k = blockCountAtLeast (Finset.univ.val.map s) k) ∧
        blockCountExactly (Finset.univ.val.map s) k =
          informationLossLayer tau k - informationLossLayer tau (k + 1) ∧
        totalInformationLoss tau = Nat.card Y - Nat.card (PeriodicCore tau) := by
  classical
  let := Fintype.ofFinite Y
  let : AddCommGroup (transientSubspace tau (Nat.card Y)) :=
    (transientSubspace tau (Nat.card Y)).addCommGroup
  let : Module ℂ (transientSubspace tau (Nat.card Y)) :=
    (transientSubspace tau (Nat.card Y)).module
  have hmodel := transfer_zero_blocks_model_fitting_zero_eigenspace tau
  obtain ⟨ι, hι, s, b, hb, hrank⟩ :=
    nilpotent_jordan_chains_rank (K := ℂ) (V := transientSubspace tau (Nat.card Y))
      (transientTransfer tau (Nat.card Y)) hmodel.2.1
  let blocks : BlockMultiset := Finset.univ.val.map s
  have hdim : blockProfileDimension blocks =
      Module.finrank ℂ (transientSubspace tau (Nat.card Y)) := by
    change ((Finset.univ.val.map s).map (fun size : ℕ+ => size.val)).sum = _
    rw [Multiset.map_map]
    simpa using (Module.finrank_eq_card_basis b).symm
  have hdimT : blockProfileDimension (transferZeroBlocks tau) =
      Module.finrank ℂ (transientSubspace tau (Nat.card Y)) := by
    exact hmodel.2.2.1.trans (LinearEquiv.finrank_eq
      (LinearEquiv.ofEq _ _ hmodel.1)).symm
  have heq : blocks = transferZeroBlocks tau := by
    apply profiles_eq (hdim.trans hdimT.symm)
    intro k
    exact (chain_profile_kernel (K := ℂ) (V := transientSubspace tau (Nat.card Y)) (ι := ι)
      (transientTransfer tau (Nat.card Y)) s b hrank k).trans
      (hmodel.2.2.2.2 k).symm
  refine ⟨ι, hι, s, b, hb, heq, ?_⟩
  intro k hk
  change _ ∧ blockCountExactly blocks k = _ ∧ _
  change (_ ∧ informationLossLayer tau k = blockCountAtLeast blocks k) ∧ _
  rw [heq]
  exact information_loss_layers_and_zero_jordan_chains tau k hk

end

end D5.S3.ObserverMemory.FunctionalGraphs.ActualTransferJordanChains

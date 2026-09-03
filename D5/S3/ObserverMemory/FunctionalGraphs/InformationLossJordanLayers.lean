/- GID: D5/S3/ObserverMemory/FunctionalGraphs/InformationLossJordanLayers
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FunctionalGraphs/InformationLossJordanLayers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Observable losses equal transfer-rank drops and zero-block layers, with exact total. -/

import D5.S3.ContinuousObservables.TransientObservableFilter
import D5.S3.ObserverMemory.FunctionalGraphs.TraceRankJordanRecovery

/- Library-search audit trail (2026-09-03):
   * Repository exact hits supply the observable algebra, canonical transfer operator,
     periodic core, stable-image theorem, and rank-difference zero-block theorem used below.
   * Pinned Mathlib exact hit `Finset.sum_range_tsub` supplies Nat-valued telescoping.
   * Pinned-Mathlib and Loogle searches found no Jordan canonical-form/block API.
     External GitHub code search required authentication and grep.app returned HTTP 503.
   * The complete receipt, including reverse and trivialization probes, is `/tmp/SEARCH-af.md`.
-/

namespace D5.S3.ObserverMemory.FunctionalGraphs.InformationLossJordanLayers

open D5.S3.ContinuousObservables.TransientObservableFilter
open D5.S3.Estimation.ExperimentCost.KernelTowerNilpotentRecovery
open D5.S3.ObserverMemory.FunctionalGraphs.TraceRankJordanRecovery
open D5.S3.ObserverMemory.InverseLimits.IdentityFuturePastGap
open D5.S3.ObserverMemory.InverseLimits.StableImagePeriodicCore
open D5.S3.ObserverMemory.InverseLimits.TraceRankCombinatorics

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

noncomputable section

/-- Source lines 1302-1307: the loss at positive step `k` is the drop in the
cardinality of the iterated image from `k - 1` to `k`. -/
def informationLossLayer {Y : Type*} [Finite Y] (tau : Y -> Y) (k : Nat) : Nat :=
  Nat.card (Set.range (tau^[k.pred])) - Nat.card (Set.range (tau^[k]))

/-- Source lines 1324-1327: the infinite loss sum is represented by its finite
support through the source's stabilization bound `Nat.card Y`. -/
def totalInformationLoss {Y : Type*} [Finite Y] (tau : Y -> Y) : Nat :=
  ∑ i ∈ Finset.range (Nat.card Y), informationLossLayer tau (i + 1)

private theorem periodic_core_card_le_rank
    {Y : Type*} [Finite Y] (tau : Y -> Y) (k : Nat) :
    Nat.card (PeriodicCore tau) ≤
      Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k)) := by
  classical
  letI := Fintype.ofFinite Y
  have hsubset : Function.periodicPts tau ⊆ Set.range (tau^[k]) := by
    intro y hy
    rcases hy with ⟨period, hperiodPos, hperiod⟩
    apply Function.periodicPts_subset_range
    exact Function.mk_mem_periodicPts hperiodPos (hperiod.iterate k)
  have hcard : (Function.periodicPts tau).ncard ≤
      (Set.range (tau^[k])).ncard :=
    Set.ncard_le_ncard hsubset
  have hrank := (transient_observable_filter tau k).2.2.2.2
  rw [hrank]
  exact hcard

private theorem information_loss_eq_rank_drop
    {Y : Type*} [Finite Y] (tau : Y -> Y) (k : Nat) :
    informationLossLayer tau k =
      Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k.pred)) -
        Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k)) := by
  have hprev := (transient_observable_filter tau k.pred).2.2.2.2
  have hcurrent := (transient_observable_filter tau k).2.2.2.2
  rw [informationLossLayer, ← hprev, ← hcurrent]

private theorem information_loss_eq_residual_rank_drop
    {Y : Type*} [Finite Y] (tau : Y -> Y) (k : Nat) :
    informationLossLayer tau k =
      (Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k.pred)) -
          Nat.card (PeriodicCore tau)) -
        (Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k)) -
          Nat.card (PeriodicCore tau)) := by
  rw [information_loss_eq_rank_drop]
  have hcore := periodic_core_card_le_rank tau k
  omega

private theorem total_information_loss_telescope
    {Y : Type*} [Finite Y] (tau : Y -> Y) :
    totalInformationLoss tau = Nat.card Y - Nat.card (PeriodicCore tau) := by
  classical
  letI := Fintype.ofFinite Y
  let imageCard : Nat -> Nat := fun j => Nat.card (Set.range (tau^[j]))
  let accumulated : Nat -> Nat := fun j => Nat.card Y - imageCard j
  have hImageAntitone : Antitone imageCard := by
    intro m n hmn
    change (Set.range (tau^[n])).ncard ≤ (Set.range (tau^[m])).ncard
    exact (iterate_range_card_antitone_and_stable tau).1 hmn
  have hAccumulatedMonotone : Monotone accumulated := by
    intro m n hmn
    exact Nat.sub_le_sub_left (hImageAntitone hmn) _
  have hsummand : ∀ i,
      informationLossLayer tau (i + 1) =
        accumulated (i + 1) - accumulated i := by
    intro i
    have hstep : imageCard (i + 1) ≤ imageCard i :=
      hImageAntitone (Nat.le_succ i)
    have hbound : imageCard i ≤ Nat.card Y := by
      change (Set.range (tau^[i])).ncard ≤ Nat.card Y
      exact Set.ncard_le_card _
    dsimp only [imageCard] at hstep hbound
    simp only [informationLossLayer, Nat.pred_eq_of_eq_succ rfl]
    dsimp only [accumulated, imageCard]
    omega
  calc
    totalInformationLoss tau =
        ∑ i ∈ Finset.range (Nat.card Y),
          (accumulated (i + 1) - accumulated i) := by
      rw [totalInformationLoss]
      apply Finset.sum_congr rfl
      intro i _
      exact hsummand i
    _ = accumulated (Nat.card Y) - accumulated 0 :=
      Finset.sum_range_tsub hAccumulatedMonotone (Nat.card Y)
    _ = Nat.card Y - Nat.card (PeriodicCore tau) := by
      have hstable : Set.range (tau^[Nat.card Y]) =
          Function.periodicPts tau :=
        (iterate_range_card_antitone_and_stable tau).2 (Nat.card Y) (by
          simpa only [Nat.card_eq_fintype_card] using
            (le_refl (Fintype.card Y)))
      have hzero : Set.range (tau^[0]) = Set.univ := by simp
      dsimp only [accumulated, imageCard]
      rw [hstable, hzero]
      simp [PeriodicCore]

private theorem information_loss_layers_full
    {Y : Type*} [Finite Y] (tau : Y -> Y) (zeroBlocks : BlockMultiset)
    (hZeroBlockRanks : ∀ j,
      Module.finrank ℂ (LinearMap.range (transferOperator tau ^ j)) -
          Nat.card (PeriodicCore tau) =
        blockProfileDimension zeroBlocks - blockKernelTower zeroBlocks j)
    (k : Nat) (hk : 0 < k) :
    (informationLossLayer tau k =
          Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k.pred)) -
            Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k)) ∧
      informationLossLayer tau k = blockCountAtLeast zeroBlocks k) ∧
      blockCountExactly zeroBlocks k =
        informationLossLayer tau k - informationLossLayer tau (k + 1) ∧
      totalInformationLoss tau = Nat.card Y - Nat.card (PeriodicCore tau) := by
  have hRankDrop := information_loss_eq_rank_drop tau k
  have hResidualDrop := information_loss_eq_residual_rank_drop tau k
  have hNextResidualDrop :=
    information_loss_eq_residual_rank_drop tau (k + 1)
  have hBlocks :=
    rank_difference_recovers_zero_blocks tau zeroBlocks hZeroBlockRanks k hk
  dsimp only at hBlocks
  have hAtLeast : informationLossLayer tau k =
      blockCountAtLeast zeroBlocks k :=
    hResidualDrop.trans hBlocks.1
  have hExactly : blockCountExactly zeroBlocks k =
      informationLossLayer tau k - informationLossLayer tau (k + 1) := by
    calc
      blockCountExactly zeroBlocks k =
          ((Module.finrank ℂ
                (LinearMap.range (transferOperator tau ^ k.pred)) -
              Nat.card (PeriodicCore tau)) -
            (Module.finrank ℂ
                (LinearMap.range (transferOperator tau ^ k)) -
              Nat.card (PeriodicCore tau))) -
          ((Module.finrank ℂ
                (LinearMap.range (transferOperator tau ^ (k + 1).pred)) -
              Nat.card (PeriodicCore tau)) -
            (Module.finrank ℂ
                (LinearMap.range (transferOperator tau ^ (k + 1))) -
              Nat.card (PeriodicCore tau))) := hBlocks.2
      _ = informationLossLayer tau k - informationLossLayer tau (k + 1) := by
        rw [← hResidualDrop, ← hNextResidualDrop]
  exact ⟨⟨hRankDrop, hAtLeast⟩, hExactly,
    total_information_loss_telescope tau⟩

/-- Source theorem 16.7, conditional on the already formalized theorem 8.3
zero-block profile equation.  The four equality leaves retain the source's
three clauses: the first clause is the two-equality rank/Jordan chain. -/
theorem information_loss_layers_and_zero_jordan_chains
    {Y : Type*} [Finite Y] (tau : Y -> Y) (zeroBlocks : BlockMultiset)
    (hZeroBlockRanks : ∀ j,
      Module.finrank ℂ (LinearMap.range (transferOperator tau ^ j)) -
          Nat.card (PeriodicCore tau) =
        blockProfileDimension zeroBlocks - blockKernelTower zeroBlocks j)
    (k : Nat) (hk : 0 < k) :
    (informationLossLayer tau k =
          Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k.pred)) -
            Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k)) ∧
      informationLossLayer tau k = blockCountAtLeast zeroBlocks k) ∧
      blockCountExactly zeroBlocks k =
        informationLossLayer tau k - informationLossLayer tau (k + 1) ∧
      totalInformationLoss tau = Nat.card Y - Nat.card (PeriodicCore tau) := by
  exact information_loss_layers_full tau zeroBlocks hZeroBlockRanks k hk

/- Reverse probe for all three source clauses. Replacing the public conclusion
with `True`, or deleting any A1/A2/A3 clause, leaves this example unprovable. -/
example {Y : Type*} [Finite Y] (tau : Y -> Y) (zeroBlocks : BlockMultiset)
    (hZeroBlockRanks : ∀ j,
      Module.finrank ℂ (LinearMap.range (transferOperator tau ^ j)) -
          Nat.card (PeriodicCore tau) =
        blockProfileDimension zeroBlocks - blockKernelTower zeroBlocks j)
    (k : Nat) (hk : 0 < k) :
    Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k.pred)) -
          Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k)) =
        blockCountAtLeast zeroBlocks k ∧
      blockCountExactly zeroBlocks k =
        informationLossLayer tau k - informationLossLayer tau (k + 1) ∧
      totalInformationLoss tau = Nat.card Y - Nat.card (PeriodicCore tau) := by
  obtain ⟨⟨hlossRank, hlossBlocks⟩, hexact, htotal⟩ :=
    information_loss_layers_and_zero_jordan_chains tau zeroBlocks
      hZeroBlockRanks k hk
  exact ⟨hlossRank.symm.trans hlossBlocks, hexact, htotal⟩

/- Trivialization probes for the degenerate finite self-maps allowed by the source. -/
example (tau : Empty -> Empty) (k : Nat) :
    informationLossLayer tau k = 0 ∧ totalInformationLoss tau = 0 := by
  simp [informationLossLayer, totalInformationLoss]

example {Y : Type*} [Finite Y] (k : Nat) :
    informationLossLayer (id : Y -> Y) k = 0 ∧
      totalInformationLoss (id : Y -> Y) = 0 := by
  simp [informationLossLayer, totalInformationLoss]

example {Y : Type*} [Finite Y] (tau : Equiv.Perm Y) (k : Nat) :
    informationLossLayer (tau : Y -> Y) k = 0 ∧
      totalInformationLoss (tau : Y -> Y) = 0 ∧
      Nat.card (PeriodicCore (tau : Y -> Y)) = Nat.card Y := by
  classical
  letI := Fintype.ofFinite Y
  have hrange : ∀ j, Set.range ((tau : Y -> Y)^[j]) = Set.univ := by
    intro j
    exact Set.range_eq_univ.mpr (tau.surjective.iterate j)
  have hstable : Set.range ((tau : Y -> Y)^[Nat.card Y]) =
      Function.periodicPts (tau : Y -> Y) :=
    (iterate_range_card_antitone_and_stable (tau : Y -> Y)).2
      (Nat.card Y) (by
        simpa only [Nat.card_eq_fintype_card] using
          (le_refl (Fintype.card Y)))
  constructor
  · simp [informationLossLayer, hrange]
  constructor
  · simp [totalInformationLoss, informationLossLayer, hrange]
  · rw [PeriodicCore, ← hstable, hrange]
    simp

end

end D5.S3.ObserverMemory.FunctionalGraphs.InformationLossJordanLayers

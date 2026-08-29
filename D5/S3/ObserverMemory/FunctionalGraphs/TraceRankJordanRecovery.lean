/- GID: D5/S3/ObserverMemory/FunctionalGraphs/TraceRankJordanRecovery
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FunctionalGraphs/TraceRankJordanRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete transfer traces and ranks recover the periodic and zero-block profiles. -/

import D5.S3.ObserverMemory.FunctionalGraphs.FiniteFunctionalGraphFittingDecomposition
import D5.S3.Estimation.ExperimentCost.KernelTowerNilpotentRecovery
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Trace-rank Jordan recovery

The zero-block multiset is tied publicly to the canonical transfer operator by
its complete residual-rank equation.  Natural-number subtraction then converts
successive residual ranks into kernel increments, where the frozen profile
theorems identify the counts of blocks of at least and exactly a given size.
-/

namespace D5.S3.ObserverMemory.FunctionalGraphs.TraceRankJordanRecovery

open D5.S3.ObserverMemory.InverseLimits.IdentityFuturePastGap
open D5.S3.ObserverMemory.InverseLimits.StableImagePeriodicCore
open D5.S3.ObserverMemory.InverseLimits.TraceRankCombinatorics
open D5.S3.Estimation.ExperimentCost.KernelTowerNilpotentRecovery

private theorem block_kernel_tower_le_dimension
    (blocks : BlockMultiset) (k : Nat) :
    blockKernelTower blocks k <= blockProfileDimension blocks := by
  induction blocks using Multiset.induction_on with
  | empty => simp [blockKernelTower, blockProfileDimension]
  | @cons size blocks ih =>
      simp only [blockKernelTower, blockProfileDimension, Multiset.map_cons,
        Multiset.sum_cons]
      exact Nat.add_le_add (Nat.min_le_right _ _) ih

private theorem block_kernel_tower_mono
    (blocks : BlockMultiset) {j k : Nat} (hjk : j <= k) :
    blockKernelTower blocks j <= blockKernelTower blocks k := by
  induction blocks using Multiset.induction_on with
  | empty => simp [blockKernelTower]
  | @cons size blocks ih =>
      simp only [blockKernelTower, Multiset.map_cons, Multiset.sum_cons]
      exact Nat.add_le_add (min_le_min hjk (le_refl _)) ih

private theorem cycle_counts_unique_of_divisor_sums
    (left right : Nat -> Nat) (hzeroLeft : left 0 = 0)
    (hzeroRight : right 0 = 0)
    (hsums : forall n, 0 < n ->
      (∑ d ∈ n.divisors, ((d * left d : Nat) : ℂ)) =
        ∑ d ∈ n.divisors, ((d * right d : Nat) : ℂ)) :
    left = right := by
  funext n
  by_cases hn0 : n = 0
  · subst n
    rw [hzeroLeft, hzeroRight]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  let fLeft : Nat -> ℂ := fun d => ((d * left d : Nat) : ℂ)
  let fRight : Nat -> ℂ := fun d => ((d * right d : Nat) : ℂ)
  let g : Nat -> ℂ := fun m => ∑ d ∈ m.divisors, fLeft d
  have hInvLeft :=
    (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
      (R := ℂ) (f := fLeft) (g := g)).mp (by
        intro m hm
        rfl)
  have hInvRight :=
    (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
      (R := ℂ) (f := fRight) (g := g)).mp (by
        intro m hm
        exact (hsums m hm).symm)
  have hCast : ((n * left n : Nat) : ℂ) = ((n * right n : Nat) : ℂ) := by
    change fLeft n = fRight n
    rw [← hInvLeft n hn, ← hInvRight n hn]
  have hMul : n * left n = n * right n := by
    exact_mod_cast hCast
  exact Nat.mul_left_cancel hn hMul

/-- For a positive index, successive residual ranks of the canonical transfer
operator count zero blocks of at least that size, and their next difference
counts blocks of exactly that size. -/
theorem rank_difference_recovers_zero_blocks
    {Y : Type*} [Finite Y] (tau : Y -> Y) (zeroBlocks : BlockMultiset)
    (hZeroBlockRanks : ∀ j,
      Module.finrank ℂ (LinearMap.range (transferOperator tau ^ j)) -
          Nat.card (PeriodicCore tau) =
        blockProfileDimension zeroBlocks - blockKernelTower zeroBlocks j)
    (k : Nat) (hk : 0 < k) :
    let a := fun j =>
      Module.finrank ℂ (LinearMap.range (transferOperator tau ^ j)) -
        Nat.card (PeriodicCore tau)
    let b := fun j => a j.pred - a j
    b k = blockCountAtLeast zeroBlocks k ∧
      blockCountExactly zeroBlocks k = b k - b (k + 1) := by
  dsimp only
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have hPrevLe : blockKernelTower zeroBlocks j <=
      blockKernelTower zeroBlocks (j + 1) :=
    block_kernel_tower_mono zeroBlocks (by omega)
  have hCurrentLe : blockKernelTower zeroBlocks (j + 1) <=
      blockProfileDimension zeroBlocks :=
    block_kernel_tower_le_dimension zeroBlocks (j + 1)
  have hNextLe : blockKernelTower zeroBlocks (j + 2) <=
      blockProfileDimension zeroBlocks :=
    block_kernel_tower_le_dimension zeroBlocks (j + 2)
  have hCurrentNext : blockKernelTower zeroBlocks (j + 1) <=
      blockKernelTower zeroBlocks (j + 2) :=
    block_kernel_tower_mono zeroBlocks (by omega)
  have hBCurrent :
      (Module.finrank ℂ
          (LinearMap.range (transferOperator tau ^ (j + 1).pred)) -
            Nat.card (PeriodicCore tau)) -
          (Module.finrank ℂ
              (LinearMap.range (transferOperator tau ^ (j + 1))) -
            Nat.card (PeriodicCore tau)) =
        kernelIncrement zeroBlocks (j + 1) := by
    rw [hZeroBlockRanks, hZeroBlockRanks, kernelIncrement]
    simp only [Nat.pred_eq_of_eq_succ rfl]
    omega
  have hBNext :
      (Module.finrank ℂ
          (LinearMap.range (transferOperator tau ^ (j + 2).pred)) -
            Nat.card (PeriodicCore tau)) -
          (Module.finrank ℂ
              (LinearMap.range (transferOperator tau ^ (j + 2))) -
            Nat.card (PeriodicCore tau)) =
        kernelIncrement zeroBlocks (j + 2) := by
    have hpred : (j + 2).pred = j + 1 := by
      calc
        (j + 2).pred = ((j + 1) + 1).pred := by
          exact congrArg Nat.pred (by omega)
        _ = j + 1 := Nat.pred_succ _
    rw [hZeroBlockRanks, hZeroBlockRanks, kernelIncrement]
    rw [hpred]
    omega
  constructor
  · rw [hBCurrent]
    exact kernel_increment_counts_blocks_at_least zeroBlocks j
  · rw [hBCurrent, hBNext]
    exact exact_block_count_from_successive_increments zeroBlocks (j + 1)

/-- Complete trace and range-rank spectra uniquely determine the functional-graph
Jordan descriptor: cycle counts for the nonzero periodic part and the multiset
of nilpotent zero-block sizes.  The two profile equations publicly tie both
descriptor candidates to their canonical source transfer operators. -/
theorem trace_rank_spectra_determine_jordan_profile
    {YLeft YRight : Type*} [Finite YLeft] [Finite YRight]
    (tau : YLeft -> YLeft) (sigma : YRight -> YRight)
    (hTrace : forall r, 0 < r ->
      LinearMap.trace ℂ (YLeft →₀ ℂ) (transferOperator tau ^ r) =
        LinearMap.trace ℂ (YRight →₀ ℂ) (transferOperator sigma ^ r))
    (hRank : forall k,
      Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k)) =
        Module.finrank ℂ (LinearMap.range (transferOperator sigma ^ k)))
    (cycleCountsLeft cycleCountsRight : Nat -> Nat)
    (hCycleZeroLeft : cycleCountsLeft 0 = 0)
    (hCycleZeroRight : cycleCountsRight 0 = 0)
    (hCycleTraceLeft : forall r, 0 < r ->
      LinearMap.trace ℂ (YLeft →₀ ℂ) (transferOperator tau ^ r) =
        ∑ d ∈ r.divisors, ((d * cycleCountsLeft d : Nat) : ℂ))
    (hCycleTraceRight : forall r, 0 < r ->
      LinearMap.trace ℂ (YRight →₀ ℂ) (transferOperator sigma ^ r) =
        ∑ d ∈ r.divisors, ((d * cycleCountsRight d : Nat) : ℂ))
    (zeroBlocksLeft zeroBlocksRight : BlockMultiset)
    (hZeroRanksLeft : forall k,
      Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k)) -
          Nat.card (PeriodicCore tau) =
        blockProfileDimension zeroBlocksLeft -
          blockKernelTower zeroBlocksLeft k)
    (hZeroRanksRight : forall k,
      Module.finrank ℂ (LinearMap.range (transferOperator sigma ^ k)) -
          Nat.card (PeriodicCore sigma) =
        blockProfileDimension zeroBlocksRight -
          blockKernelTower zeroBlocksRight k) :
    cycleCountsLeft = cycleCountsRight ∧ zeroBlocksLeft = zeroBlocksRight := by
  classical
  letI : Fintype YLeft := Fintype.ofFinite YLeft
  letI : Fintype YRight := Fintype.ofFinite YRight
  have hCycles : cycleCountsLeft = cycleCountsRight :=
    cycle_counts_unique_of_divisor_sums cycleCountsLeft cycleCountsRight
      hCycleZeroLeft hCycleZeroRight (by
        intro r hr
        calc
          (∑ d ∈ r.divisors, ((d * cycleCountsLeft d : Nat) : ℂ)) =
              LinearMap.trace ℂ (YLeft →₀ ℂ)
                (transferOperator tau ^ r) := (hCycleTraceLeft r hr).symm
          _ = LinearMap.trace ℂ (YRight →₀ ℂ)
                (transferOperator sigma ^ r) := hTrace r hr
          _ = ∑ d ∈ r.divisors,
                ((d * cycleCountsRight d : Nat) : ℂ) := hCycleTraceRight r hr)
  let stablePower := max (Fintype.card YLeft) (Fintype.card YRight)
  have hStableLeft : Set.range (tau^[stablePower]) = Function.periodicPts tau :=
    (iterate_range_card_antitone_and_stable tau).2 stablePower (by
      exact le_max_left _ _)
  have hStableRight : Set.range (sigma^[stablePower]) =
      Function.periodicPts sigma :=
    (iterate_range_card_antitone_and_stable sigma).2 stablePower (by
      exact le_max_right _ _)
  have hRankMeaningLeft :=
    (trace_rank_combinatorial_meaning tau
      (r := ⟨1, by omega⟩) (k := stablePower)).2
  have hRankMeaningRight :=
    (trace_rank_combinatorial_meaning sigma
      (r := ⟨1, by omega⟩) (k := stablePower)).2
  rw [hStableLeft] at hRankMeaningLeft
  rw [hStableRight] at hRankMeaningRight
  have hPeriodicCard : Nat.card (PeriodicCore tau) =
      Nat.card (PeriodicCore sigma) := by
    calc
      Nat.card (PeriodicCore tau) =
          Module.finrank ℂ
            (LinearMap.range (transferOperator tau ^ stablePower)) := by
              exact hRankMeaningLeft.symm
      _ = Module.finrank ℂ
            (LinearMap.range (transferOperator sigma ^ stablePower)) :=
              hRank stablePower
      _ = Nat.card (PeriodicCore sigma) := hRankMeaningRight
  have hZeroLeftAtZero :
      Module.finrank ℂ (LinearMap.range (transferOperator tau ^ 0)) -
          Nat.card (PeriodicCore tau) =
        blockProfileDimension zeroBlocksLeft := by
    simpa [blockKernelTower] using hZeroRanksLeft 0
  have hZeroRightAtZero :
      Module.finrank ℂ (LinearMap.range (transferOperator sigma ^ 0)) -
          Nat.card (PeriodicCore sigma) =
        blockProfileDimension zeroBlocksRight := by
    simpa [blockKernelTower] using hZeroRanksRight 0
  have hDimension : blockProfileDimension zeroBlocksLeft =
      blockProfileDimension zeroBlocksRight := by
    rw [← hZeroLeftAtZero, ← hZeroRightAtZero, hRank 0, hPeriodicCard]
  have hTower : forall k, blockKernelTower zeroBlocksLeft k =
      blockKernelTower zeroBlocksRight k := by
    intro k
    have hLeft := hZeroRanksLeft k
    have hRight := hZeroRanksRight k
    have hLeftBound := block_kernel_tower_le_dimension zeroBlocksLeft k
    have hRightBound := block_kernel_tower_le_dimension zeroBlocksRight k
    have hRankEq := hRank k
    omega
  have hZeroBlocks : zeroBlocksLeft = zeroBlocksRight := by
    apply Multiset.ext.mpr
    intro size
    calc
      zeroBlocksLeft.count size = blockCountExactly zeroBlocksLeft size.1 := by
        simp [Multiset.count, blockCountExactly, Subtype.ext_iff, eq_comm]
      _ = kernelIncrement zeroBlocksLeft size.1 -
          kernelIncrement zeroBlocksLeft (size.1 + 1) :=
        exact_block_count_from_successive_increments zeroBlocksLeft size.1
      _ = kernelIncrement zeroBlocksRight size.1 -
          kernelIncrement zeroBlocksRight (size.1 + 1) := by
        simp only [kernelIncrement, hTower]
      _ = blockCountExactly zeroBlocksRight size.1 :=
        (exact_block_count_from_successive_increments
          zeroBlocksRight size.1).symm
      _ = zeroBlocksRight.count size := by
        simp [Multiset.count, blockCountExactly, Subtype.ext_iff, eq_comm]
  exact ⟨hCycles, hZeroBlocks⟩

end D5.S3.ObserverMemory.FunctionalGraphs.TraceRankJordanRecovery

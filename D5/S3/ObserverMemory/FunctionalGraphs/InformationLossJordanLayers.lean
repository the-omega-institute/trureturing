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
     periodic core, stable-image theorem, and Fitting decomposition used below.
   * Pinned Mathlib exact hit `Finset.sum_range_tsub` supplies Nat-valued telescoping.
   * The requested `Module.End.iSup_ker_pow_eq_top` is absent.  Pinned Mathlib instead
     supplies `Module.End.ker_pow_le_ker_pow_finrank` and
     `Module.End.ker_pow_eq_ker_pow_finrank_of_le`; the latter is already exercised by
     `KernelTowerNilpotentRecovery.matrix_kernel_tower_stabilizes_at_dimension`.
   * Searches for successive-kernel quotient dimensions, conjugate integer partitions,
     and Jordan canonical-form/block APIs found no declaration closing theorem 8.3.
     The construction below therefore forms the conjugate partition of the actual rank
     losses and proves that its tower is exactly `finrank (ker (L_tau ^ k))`.
   External GitHub code search required authentication and grep.app returned HTTP 503.
-/

namespace D5.S3.ObserverMemory.FunctionalGraphs.InformationLossJordanLayers

open D5.S3.ContinuousObservables.TransientObservableFilter
open D5.S3.Estimation.ExperimentCost.KernelTowerNilpotentRecovery
open D5.S3.ObserverMemory.FunctionalGraphs.TraceRankJordanRecovery
open D5.S3.ObserverMemory.FunctionalGraphs.FiniteFunctionalGraphFittingDecomposition
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

private def lossSequence {Y : Type*} [Finite Y] (tau : Y -> Y) (i : Nat) : Nat :=
  informationLossLayer tau (i + 1)

private theorem countP_replicate_eq {A : Type*} (predicate : A -> Prop)
    [DecidablePred predicate] (n : Nat) (value : A) :
    (Multiset.replicate n value).countP predicate =
      if predicate value then n else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Multiset.replicate_succ, Multiset.countP_cons, ih]
      by_cases h : predicate value <;> simp [h]

private def blocksOfAntitoneLayers (layers : Nat -> Nat) (n : Nat) :
    BlockMultiset :=
  ∑ i ∈ Finset.range n,
    Multiset.replicate (layers i - layers (i + 1))
      (⟨i + 1, by omega⟩ : PositiveBlockSize)

private theorem count_at_least_blocks_of_antitone_layers
    (layers : Nat -> Nat) (hlayers : Antitone layers)
    (n k : Nat) (hk : 0 < k) :
    blockCountAtLeast (blocksOfAntitoneLayers layers n) k =
      if k ≤ n then layers k.pred - layers n else 0 := by
  induction n with
  | zero =>
      simp [blocksOfAntitoneLayers, blockCountAtLeast, show k ≠ 0 by omega]
  | succ n ih =>
      rw [blocksOfAntitoneLayers, Finset.sum_range_succ, blockCountAtLeast,
        Multiset.countP_add]
      change blockCountAtLeast (blocksOfAntitoneLayers layers n) k + _ = _
      rw [ih, countP_replicate_eq]
      by_cases hkn : k ≤ n
      · have hpred : k.pred ≤ n := (Nat.pred_le k).trans hkn
        have hn : layers n ≥ layers (n + 1) := hlayers (Nat.le_succ n)
        have hstart : layers k.pred ≥ layers n := hlayers hpred
        have hknew : k ≤ n + 1 := hkn.trans (Nat.le_succ n)
        rw [if_pos hkn, if_pos hknew, if_pos hknew]
        omega
      · by_cases hknew : k ≤ n + 1
        · have hkeq : k = n + 1 := by omega
          subst k
          simp [hkn]
        · simp [hkn, hknew]

private theorem min_succ_eq_add_indicator (k size : Nat) :
    min (k + 1) size = min k size + if k + 1 ≤ size then 1 else 0 := by
  by_cases h : k + 1 ≤ size
  · rw [if_pos h, Nat.min_eq_left h, Nat.min_eq_left (by omega)]
  · rw [if_neg h, Nat.min_eq_right (by omega),
      Nat.min_eq_right (by omega)]
    simp

private theorem block_kernel_tower_succ (blocks : BlockMultiset) (k : Nat) :
    blockKernelTower blocks (k + 1) =
      blockKernelTower blocks k + blockCountAtLeast blocks (k + 1) := by
  induction blocks using Multiset.induction_on with
  | empty => simp [blockKernelTower, blockCountAtLeast]
  | @cons size blocks ih =>
      simp only [blockKernelTower, Multiset.map_cons, Multiset.sum_cons,
        blockCountAtLeast, Multiset.countP_cons]
      have ih' : (blocks.map fun size => min (k + 1) size.1).sum =
          (blocks.map fun size => min k size.1).sum +
            blocks.countP (fun size => k + 1 ≤ size.1) := by
        simpa [blockKernelTower, blockCountAtLeast] using ih
      rw [min_succ_eq_add_indicator, ih']
      split <;> omega

private theorem block_kernel_tower_eq_dimension_of_count_zero
    (blocks : BlockMultiset) (n : Nat)
    (hzero : blockCountAtLeast blocks (n + 1) = 0) :
    blockKernelTower blocks n = blockProfileDimension blocks := by
  induction blocks using Multiset.induction_on with
  | empty => simp [blockKernelTower, blockProfileDimension]
  | @cons size blocks ih =>
      simp only [blockCountAtLeast, Multiset.countP_cons] at hzero
      have hhead : ¬ n + 1 ≤ size.1 := by
        by_contra hle
        simp [hle] at hzero
      have htail : blockCountAtLeast blocks (n + 1) = 0 := by
        simpa [blockCountAtLeast, hhead] using hzero
      have hsize : size.1 ≤ n := by omega
      simp only [blockKernelTower, blockProfileDimension, Multiset.map_cons,
        Multiset.sum_cons]
      rw [Nat.min_eq_right hsize]
      exact congrArg (size.1 + ·) (ih htail)

/-- The zero-block multiset of the canonical transfer operator.  Its exact-size
multiplicity is constructed from consecutive actual rank losses, through the
finite stabilization bound `Nat.card Y`. -/
def transferZeroBlocks {Y : Type*} [Finite Y] (tau : Y -> Y) : BlockMultiset :=
  blocksOfAntitoneLayers (lossSequence tau) (Nat.card Y)

private theorem range_pow_succ_le {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (k : Nat) :
    LinearMap.range (f ^ (k + 1)) ≤ LinearMap.range (f ^ k) := by
  rw [pow_succ, Module.End.mul_eq_comp]
  exact LinearMap.range_comp_le_range _ _

private theorem restricted_range_eq_pow_succ {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (k : Nat) :
    LinearMap.range (f.domRestrict (LinearMap.range (f ^ k))) =
      LinearMap.range (f ^ (k + 1)) := by
  calc
    LinearMap.range (f.domRestrict (LinearMap.range (f ^ k))) =
        (LinearMap.range (f ^ k)).map f := LinearMap.range_domRestrict _ _
    _ = LinearMap.range (f.comp (f ^ k)) :=
      (LinearMap.range_comp (f ^ k) f).symm
    _ = LinearMap.range (f ^ (k + 1)) := by
      rw [← Module.End.mul_eq_comp, ← pow_succ']

private theorem rank_drop_eq_restricted_kernel {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (k : Nat) :
    Module.finrank K (LinearMap.range (f ^ k)) -
        Module.finrank K (LinearMap.range (f ^ (k + 1))) =
      Module.finrank K
        (LinearMap.ker (f.domRestrict (LinearMap.range (f ^ k)))) := by
  have hnullity :=
    (f.domRestrict (LinearMap.range (f ^ k))).finrank_range_add_finrank_ker
  rw [restricted_range_eq_pow_succ] at hnullity
  omega

private def restrictedKernelInclusion {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (f : Module.End K V)
    {p q : Submodule K V} (hpq : p ≤ q) :
    LinearMap.ker (f.domRestrict p) →ₗ[K]
      LinearMap.ker (f.domRestrict q) where
  toFun x := ⟨⟨x.1.1, hpq x.1.2⟩, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem restricted_kernel_inclusion_injective
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) {p q : Submodule K V} (hpq : p ≤ q) :
    Function.Injective (restrictedKernelInclusion f hpq) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z => z.1.1) hxy

private theorem rank_drop_antitone {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (k : Nat) :
    Module.finrank K (LinearMap.range (f ^ (k + 1))) -
        Module.finrank K (LinearMap.range (f ^ (k + 2))) ≤
      Module.finrank K (LinearMap.range (f ^ k)) -
        Module.finrank K (LinearMap.range (f ^ (k + 1))) := by
  rw [rank_drop_eq_restricted_kernel, rank_drop_eq_restricted_kernel]
  exact LinearMap.finrank_le_finrank_of_injective
    (restricted_kernel_inclusion_injective f (range_pow_succ_le f k))

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

private theorem loss_sequence_antitone
    {Y : Type*} [Finite Y] (tau : Y -> Y) :
    Antitone (lossSequence tau) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [lossSequence, lossSequence,
    information_loss_eq_rank_drop, information_loss_eq_rank_drop]
  simpa using rank_drop_antitone (transferOperator tau) k

private theorem information_loss_eq_zero_after_card
    {Y : Type*} [Finite Y] (tau : Y -> Y) {k : Nat}
    (hk : Nat.card Y < k) : informationLossLayer tau k = 0 := by
  classical
  letI := Fintype.ofFinite Y
  have hpred : Fintype.card Y ≤ k.pred := by
    simpa only [Nat.card_eq_fintype_card] using
      Nat.le_pred_of_lt hk
  have hcurrent : Fintype.card Y ≤ k := by
    simpa only [Nat.card_eq_fintype_card] using
      (show Nat.card Y ≤ k by omega)
  have hstablePred :=
    (iterate_range_card_antitone_and_stable tau).2 k.pred hpred
  have hstableCurrent :=
    (iterate_range_card_antitone_and_stable tau).2 k hcurrent
  rw [informationLossLayer, hstablePred, hstableCurrent]
  omega

/-- The blocks constructed from the transfer operator satisfy theorem 8.3's
first conclusion: every positive rank loss counts the blocks of at least that
size.  No block profile or rank equation is supplied by the caller. -/
theorem transfer_zero_blocks_count_at_least
    {Y : Type*} [Finite Y] (tau : Y -> Y) (k : Nat) (hk : 0 < k) :
    blockCountAtLeast (transferZeroBlocks tau) k =
      informationLossLayer tau k := by
  rw [transferZeroBlocks,
    count_at_least_blocks_of_antitone_layers
      (lossSequence tau) (loss_sequence_antitone tau) (Nat.card Y) k hk]
  by_cases hkn : k ≤ Nat.card Y
  · rw [if_pos hkn]
    have hlast : informationLossLayer tau (Nat.card Y + 1) = 0 :=
      information_loss_eq_zero_after_card tau (by omega)
    have hkpred : k.pred + 1 = k := by
      simpa only [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hk
    simp only [lossSequence]
    rw [hkpred, hlast, Nat.sub_zero]
  · rw [if_neg hkn]
    exact (information_loss_eq_zero_after_card tau (by omega)).symm

private theorem ker_pow_succ_le {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (f : Module.End K V) (k : Nat) :
    LinearMap.ker (f ^ k) ≤ LinearMap.ker (f ^ (k + 1)) := by
  rw [pow_succ', Module.End.mul_eq_comp]
  exact LinearMap.ker_le_ker_comp _ _

private theorem transfer_kernel_increment_eq_information_loss
    {Y : Type*} [Finite Y] (tau : Y -> Y) (k : Nat) :
    Module.finrank ℂ (LinearMap.ker (transferOperator tau ^ (k + 1))) -
        Module.finrank ℂ (LinearMap.ker (transferOperator tau ^ k)) =
      informationLossLayer tau (k + 1) := by
  have hcurrent :=
    (transferOperator tau ^ k).finrank_range_add_finrank_ker
  have hnext :=
    (transferOperator tau ^ (k + 1)).finrank_range_add_finrank_ker
  have hker : Module.finrank ℂ
        (LinearMap.ker (transferOperator tau ^ k)) ≤
      Module.finrank ℂ
        (LinearMap.ker (transferOperator tau ^ (k + 1))) :=
    Submodule.finrank_mono (ker_pow_succ_le (transferOperator tau) k)
  have hloss := information_loss_eq_rank_drop tau (k + 1)
  have hpred : (k + 1).pred = k := Nat.pred_succ k
  rw [hpred] at hloss
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

/-- The constructed multiset is tied to the actual generalized zero-eigenspace:
its abstract kernel tower equals the dimensions of the kernels of every power
of the canonical transfer operator. -/
theorem transfer_zero_blocks_kernel_tower
    {Y : Type*} [Finite Y] (tau : Y -> Y) (k : Nat) :
    blockKernelTower (transferZeroBlocks tau) k =
      Module.finrank ℂ (LinearMap.ker (transferOperator tau ^ k)) := by
  induction k with
  | zero =>
      rw [pow_zero, Module.End.one_eq_id, LinearMap.ker_id]
      simp [blockKernelTower]
  | succ k ih =>
      rw [block_kernel_tower_succ, ih,
        transfer_zero_blocks_count_at_least tau (k + 1) (by omega)]
      have hincrement := transfer_kernel_increment_eq_information_loss tau k
      have hker : Module.finrank ℂ
            (LinearMap.ker (transferOperator tau ^ k)) ≤
          Module.finrank ℂ
            (LinearMap.ker (transferOperator tau ^ (k + 1))) :=
        Submodule.finrank_mono (ker_pow_succ_le (transferOperator tau) k)
      omega

/-- The constructed blocks have exactly the dimension of the stabilized
generalized zero-eigenspace of the transfer operator. -/
theorem transfer_zero_blocks_profile_dimension
    {Y : Type*} [Finite Y] (tau : Y -> Y) :
    blockProfileDimension (transferZeroBlocks tau) =
      Module.finrank ℂ
        (LinearMap.ker (transferOperator tau ^ Nat.card Y)) := by
  have hcount := transfer_zero_blocks_count_at_least tau
    (Nat.card Y + 1) (by omega)
  have hloss : informationLossLayer tau (Nat.card Y + 1) = 0 :=
    information_loss_eq_zero_after_card tau (by omega)
  rw [hloss] at hcount
  have htower := block_kernel_tower_eq_dimension_of_count_zero
    (transferZeroBlocks tau) (Nat.card Y) hcount
  exact htower.symm.trans (transfer_zero_blocks_kernel_tower tau (Nat.card Y))

private theorem transfer_rank_at_card_eq_periodic_core_card
    {Y : Type*} [Finite Y] (tau : Y -> Y) :
    Module.finrank ℂ
        (LinearMap.range (transferOperator tau ^ Nat.card Y)) =
      Nat.card (PeriodicCore tau) := by
  classical
  letI := Fintype.ofFinite Y
  have hrank := (transient_observable_filter tau (Nat.card Y)).2.2.2.2
  have hstable : Set.range (tau^[Nat.card Y]) = Function.periodicPts tau :=
    (iterate_range_card_antitone_and_stable tau).2 (Nat.card Y) (by
      simpa only [Nat.card_eq_fintype_card] using
        (le_refl (Fintype.card Y)))
  rw [hrank, hstable]

private theorem transfer_zero_blocks_dimension_eq_transient_card
    {Y : Type*} [Finite Y] (tau : Y -> Y) :
    blockProfileDimension (transferZeroBlocks tau) =
      Nat.card Y - Nat.card (PeriodicCore tau) := by
  classical
  letI := Fintype.ofFinite Y
  have hnullity :=
    (transferOperator tau ^ Nat.card Y).finrank_range_add_finrank_ker
  have hrank := transfer_rank_at_card_eq_periodic_core_card tau
  have hprofile := transfer_zero_blocks_profile_dimension tau
  have hambient : Module.finrank ℂ (Y →₀ ℂ) = Nat.card Y := by
    simp [Nat.card_eq_fintype_card]
  omega

/-- Theorem 8.3's complete residual-rank equation, now proved for the
constructed block multiset rather than required from the caller. -/
theorem transfer_zero_blocks_rank_profile
    {Y : Type*} [Finite Y] (tau : Y -> Y) (j : Nat) :
    Module.finrank ℂ (LinearMap.range (transferOperator tau ^ j)) -
        Nat.card (PeriodicCore tau) =
      blockProfileDimension (transferZeroBlocks tau) -
        blockKernelTower (transferZeroBlocks tau) j := by
  classical
  letI := Fintype.ofFinite Y
  have hnullity :=
    (transferOperator tau ^ j).finrank_range_add_finrank_ker
  have hambient : Module.finrank ℂ (Y →₀ ℂ) = Nat.card Y := by
    simp [Nat.card_eq_fintype_card]
  have hdim := transfer_zero_blocks_dimension_eq_transient_card tau
  have htower := transfer_zero_blocks_kernel_tower tau j
  have hcore := periodic_core_card_le_rank tau j
  omega

private theorem transfer_ker_pow_le_transient_subspace
    {Y : Type*} [Finite Y] (tau : Y -> Y) (j : Nat) :
    LinearMap.ker (transferOperator tau ^ j) ≤
      transientSubspace tau (Nat.card Y) := by
  classical
  letI := Fintype.ofFinite Y
  have hstable : Set.range (tau^[Nat.card Y]) = Function.periodicPts tau :=
    (iterate_range_card_antitone_and_stable tau).2 (Nat.card Y) (by
      simpa only [Nat.card_eq_fintype_card] using
        (le_refl (Fintype.card Y)))
  rw [(finite_functional_graph_fitting_decomposition
    tau (Nat.card Y) hstable).2.1]
  have hambient : Module.finrank ℂ (Y →₀ ℂ) = Nat.card Y := by
    simp [Nat.card_eq_fintype_card]
  rw [← hambient]
  exact Module.End.ker_pow_le_ker_pow_finrank (transferOperator tau) j

private theorem transfer_maps_stable_transient
    {Y : Type*} [Finite Y] (tau : Y -> Y) :
    Set.MapsTo (transferOperator tau)
      (transientSubspace tau (Nat.card Y))
      (transientSubspace tau (Nat.card Y)) := by
  classical
  letI := Fintype.ofFinite Y
  have hstable : Set.range (tau^[Nat.card Y]) = Function.periodicPts tau :=
    (iterate_range_card_antitone_and_stable tau).2 (Nat.card Y) (by
      simpa only [Nat.card_eq_fintype_card] using
        (le_refl (Fintype.card Y)))
  rw [(finite_functional_graph_fitting_decomposition
    tau (Nat.card Y) hstable).2.1]
  intro vector hvector
  apply LinearMap.mem_ker.mpr
  have hzero := LinearMap.mem_ker.mp hvector
  calc
    (transferOperator tau ^ Nat.card Y) (transferOperator tau vector) =
        (transferOperator tau ^ (Nat.card Y + 1)) vector := by
      rw [pow_succ, Module.End.mul_apply]
    _ = transferOperator tau
        ((transferOperator tau ^ Nat.card Y) vector) := by
      rw [pow_succ', Module.End.mul_apply]
    _ = 0 := by rw [hzero, map_zero]

private theorem transient_transfer_pow_coe
    {Y : Type*} [Finite Y] (tau : Y -> Y) (j : Nat)
    (vector : transientSubspace tau (Nat.card Y)) :
    (((transientTransfer tau (Nat.card Y)) ^ j) vector).1 =
      (transferOperator tau ^ j) vector.1 := by
  rw [transientTransfer,
    Module.End.pow_restrict j (transfer_maps_stable_transient tau)]
  rfl

private noncomputable def transferKernelEquivTransientKernel
    {Y : Type*} [Finite Y] (tau : Y -> Y) (j : Nat) :
    LinearMap.ker (transferOperator tau ^ j) ≃ₗ[ℂ]
      LinearMap.ker ((transientTransfer tau (Nat.card Y)) ^ j) where
  toFun vector :=
    ⟨⟨vector.1, transfer_ker_pow_le_transient_subspace tau j vector.2⟩, by
      apply Subtype.ext
      rw [transient_transfer_pow_coe]
      exact LinearMap.mem_ker.mp vector.2⟩
  invFun vector := ⟨vector.1.1, by
    apply LinearMap.mem_ker.mpr
    have hzero := congrArg Subtype.val (LinearMap.mem_ker.mp vector.2)
    rw [transient_transfer_pow_coe] at hzero
    exact hzero⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The power kernels of the Fitting transient restriction are linearly
equivalent to the actual generalized zero kernels of the ambient transfer
operator. -/
theorem transfer_transient_kernel_finrank_eq
    {Y : Type*} [Finite Y] (tau : Y -> Y) (j : Nat) :
    Module.finrank ℂ
        (LinearMap.ker ((transientTransfer tau (Nat.card Y)) ^ j)) =
      Module.finrank ℂ (LinearMap.ker (transferOperator tau ^ j)) := by
  exact LinearEquiv.finrank_eq (transferKernelEquivTransientKernel tau j).symm

/-- Semantic certificate for the word "zero block": at the finite stabilization
exponent the Fitting transient carrier is the generalized zero-eigenspace, its
restriction is nilpotent, and `transferZeroBlocks` represents both its ambient
and restricted power-kernel dimensions. -/
theorem transfer_zero_blocks_model_fitting_zero_eigenspace
    {Y : Type*} [Finite Y] (tau : Y -> Y) :
    let n := Nat.card Y
    transientSubspace tau n =
        LinearMap.ker (transferOperator tau ^ n) ∧
      IsNilpotent (transientTransfer tau n) ∧
      blockProfileDimension (transferZeroBlocks tau) =
        Module.finrank ℂ (LinearMap.ker (transferOperator tau ^ n)) ∧
      (∀ j, blockKernelTower (transferZeroBlocks tau) j =
        Module.finrank ℂ (LinearMap.ker (transferOperator tau ^ j))) ∧
      ∀ j, blockKernelTower (transferZeroBlocks tau) j =
        Module.finrank ℂ
          (LinearMap.ker ((transientTransfer tau n) ^ j)) := by
  classical
  letI := Fintype.ofFinite Y
  dsimp only
  have hstable : Set.range (tau^[Nat.card Y]) = Function.periodicPts tau :=
    (iterate_range_card_antitone_and_stable tau).2 (Nat.card Y) (by
      simpa only [Nat.card_eq_fintype_card] using
        (le_refl (Fintype.card Y)))
  have hfitting :=
    finite_functional_graph_fitting_decomposition tau (Nat.card Y) hstable
  exact ⟨hfitting.2.1, hfitting.2.2.1,
    transfer_zero_blocks_profile_dimension tau,
    transfer_zero_blocks_kernel_tower tau, fun j =>
      (transfer_zero_blocks_kernel_tower tau j).trans
        (transfer_transient_kernel_finrank_eq tau j).symm⟩

private theorem information_loss_layers_full
    {Y : Type*} [Finite Y] (tau : Y -> Y)
    (k : Nat) (hk : 0 < k) :
    (informationLossLayer tau k =
          Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k.pred)) -
            Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k)) ∧
      informationLossLayer tau k = blockCountAtLeast (transferZeroBlocks tau) k) ∧
      blockCountExactly (transferZeroBlocks tau) k =
        informationLossLayer tau k - informationLossLayer tau (k + 1) ∧
      totalInformationLoss tau = Nat.card Y - Nat.card (PeriodicCore tau) := by
  have hRankDrop := information_loss_eq_rank_drop tau k
  have hResidualDrop := information_loss_eq_residual_rank_drop tau k
  have hNextResidualDrop :=
    information_loss_eq_residual_rank_drop tau (k + 1)
  have hBlocks :=
    rank_difference_recovers_zero_blocks tau (transferZeroBlocks tau)
      (transfer_zero_blocks_rank_profile tau) k hk
  dsimp only at hBlocks
  have hAtLeast : informationLossLayer tau k =
      blockCountAtLeast (transferZeroBlocks tau) k :=
    hResidualDrop.trans hBlocks.1
  have hExactly : blockCountExactly (transferZeroBlocks tau) k =
      informationLossLayer tau k - informationLossLayer tau (k + 1) := by
    calc
      blockCountExactly (transferZeroBlocks tau) k =
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

/-- Source theorem 16.7.  The zero-block profile is constructed above from the
actual transfer-operator kernel tower, so theorem 8.3 is discharged internally
rather than required from the caller.  The four equality leaves retain the
source's three clauses: the first clause is the two-equality rank/Jordan chain. -/
theorem information_loss_layers_and_zero_jordan_chains
    {Y : Type*} [Finite Y] (tau : Y -> Y)
    (k : Nat) (hk : 0 < k) :
    (informationLossLayer tau k =
          Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k.pred)) -
            Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k)) ∧
      informationLossLayer tau k = blockCountAtLeast (transferZeroBlocks tau) k) ∧
      blockCountExactly (transferZeroBlocks tau) k =
        informationLossLayer tau k - informationLossLayer tau (k + 1) ∧
      totalInformationLoss tau = Nat.card Y - Nat.card (PeriodicCore tau) := by
  exact information_loss_layers_full tau k hk

/- Reverse probe for all three source clauses. Replacing the public conclusion
with `True`, or deleting any A1/A2/A3 clause, leaves this example unprovable. -/
example {Y : Type*} [Finite Y] (tau : Y -> Y) (k : Nat) (hk : 0 < k) :
    Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k.pred)) -
          Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k)) =
        blockCountAtLeast (transferZeroBlocks tau) k ∧
      blockCountExactly (transferZeroBlocks tau) k =
        informationLossLayer tau k - informationLossLayer tau (k + 1) ∧
      totalInformationLoss tau = Nat.card Y - Nat.card (PeriodicCore tau) := by
  obtain ⟨⟨hlossRank, hlossBlocks⟩, hexact, htotal⟩ :=
    information_loss_layers_and_zero_jordan_chains tau k hk
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

/- Constructive probe (P6): the chain `2 -> 1 -> 0 -> 0` has one actual
zero block of size two.  Its first two rank-loss layers are one and all later
layers vanish. -/
private def threePointChain : Fin 3 -> Fin 3 := ![0, 0, 1]

private def twoBlockSize : PositiveBlockSize := ⟨2, by omega⟩

private theorem threePointChain_range_one :
    Set.range (threePointChain^[1]) = ({0, 1} : Set (Fin 3)) := by
  ext x
  fin_cases x <;> simp [threePointChain]

private theorem threePointChain_range_two :
    Set.range (threePointChain^[2]) = ({0} : Set (Fin 3)) := by
  have hconstant : threePointChain^[2] = fun _ => 0 := by
    funext x
    fin_cases x <;> rfl
  rw [hconstant]
  simp

private theorem threePointChain_range_three :
    Set.range (threePointChain^[3]) = ({0} : Set (Fin 3)) := by
  have hconstant : threePointChain^[3] = fun _ => 0 := by
    funext x
    fin_cases x <;> rfl
  rw [hconstant]
  simp

private theorem threePointChain_range_four :
    Set.range (threePointChain^[4]) = ({0} : Set (Fin 3)) := by
  have hconstant : threePointChain^[4] = fun _ => 0 := by
    funext x
    fin_cases x <;> rfl
  rw [hconstant]
  simp

example :
    transferZeroBlocks threePointChain = {twoBlockSize} ∧
      informationLossLayer threePointChain 1 = 1 ∧
      informationLossLayer threePointChain 2 = 1 ∧
      informationLossLayer threePointChain 3 = 0 ∧
      blockCountAtLeast (transferZeroBlocks threePointChain) 1 = 1 ∧
      blockCountAtLeast (transferZeroBlocks threePointChain) 2 = 1 ∧
      blockCountAtLeast (transferZeroBlocks threePointChain) 3 = 0 := by
  have hlossOne : informationLossLayer threePointChain 1 = 1 := by
    rw [informationLossLayer, threePointChain_range_one]
    norm_num
  have hlossTwo : informationLossLayer threePointChain 2 = 1 := by
    rw [informationLossLayer]
    simp only [Nat.pred_eq_of_eq_succ rfl]
    rw [threePointChain_range_one,
      threePointChain_range_two]
    norm_num
  have hlossThree : informationLossLayer threePointChain 3 = 0 := by
    rw [informationLossLayer]
    simp only [Nat.pred_eq_of_eq_succ rfl]
    rw [threePointChain_range_two,
      threePointChain_range_three]
    exact Nat.sub_self _
  have hlossFour : informationLossLayer threePointChain 4 = 0 := by
    rw [informationLossLayer]
    simp only [Nat.pred_eq_of_eq_succ rfl]
    rw [threePointChain_range_three,
      threePointChain_range_four]
    exact Nat.sub_self _
  have hblocks : transferZeroBlocks threePointChain = {twoBlockSize} := by
    simp [transferZeroBlocks, blocksOfAntitoneLayers, Finset.sum_range_succ,
      lossSequence, hlossOne, hlossTwo, hlossThree, hlossFour]
    change (0 : BlockMultiset) + {
        (⟨2, by omega⟩ : PositiveBlockSize)} + 0 = {twoBlockSize}
    simp [twoBlockSize]
  have hcountOne :=
    transfer_zero_blocks_count_at_least threePointChain 1 (by omega)
  have hcountTwo :=
    transfer_zero_blocks_count_at_least threePointChain 2 (by omega)
  have hcountThree :=
    transfer_zero_blocks_count_at_least threePointChain 3 (by omega)
  rw [hlossOne] at hcountOne
  rw [hlossTwo] at hcountTwo
  rw [hlossThree] at hcountThree
  exact ⟨hblocks, hlossOne, hlossTwo, hlossThree,
    hcountOne, hcountTwo, hcountThree⟩

end

end D5.S3.ObserverMemory.FunctionalGraphs.InformationLossJordanLayers

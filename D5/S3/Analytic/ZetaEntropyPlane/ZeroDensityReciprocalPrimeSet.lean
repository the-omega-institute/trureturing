/- GID: D5/S3/Analytic/ZetaEntropyPlane/ZeroDensityReciprocalPrimeSet
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaEntropyPlane/ZeroDensityReciprocalPrimeSet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zero-density prime support has divergent reciprocal mass and conditional completion. -/
/- Library-search audit trail (2026-09-03): repository searches for relative prime
   density, sparse prime support, reciprocal mass, Hellinger energy, Kakutani, and
   transcript-law singularity found the exact reusable `primeIndexEquiv` and
   `relativePrimeCountingRatio` declarations, but no theorem giving a zero-relative-
   density set with divergent actual `1 / p` mass or discharging the source's
   singularity/divergence bridge.
   The existing square-indexed module uses `1 / (sqrt(index) + 1)`, not `1 / p`.
   Pinned Mathlib supplies `Nat.Primes.not_summable_one_div` and the exact residue-
   class theorem `summable_indicator_mod_iff`; GitHub and Reservoir searches found
   no exact external theorem in a pinned dependency. The construction below uses
   `Nat.find` on analytic block existence to classically select successively thinner
   finite index blocks; it is noncomputable. -/

import Mathlib.Analysis.SumOverResidueClass
import D5.S3.Analytic.ZetaEntropyPlane.PrimeRelativeDensityEvidenceDivergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaEntropyPlane.ZeroDensityReciprocalPrimeSet

open Filter Finset MeasureTheory Asymptotics
open scoped Topology Nat.Prime MeasureTheory
open D5.S3.Analytic.ZetaEntropyPlane.PrimeRelativeDensityEvidenceDivergence

noncomputable section

private def indexedPrimeReciprocal (n : Nat) : Real :=
  1 / ((primeIndexEquiv n).1 : Real)

private theorem indexedPrimeReciprocal_nonneg (n : Nat) :
    0 <= indexedPrimeReciprocal n := by
  exact div_nonneg zero_le_one (Nat.cast_nonneg _)

private theorem indexedPrimeReciprocal_antitone :
    Antitone indexedPrimeReciprocal := by
  intro a b hab
  apply one_div_le_one_div_of_le
  · exact_mod_cast (primeIndexEquiv a).2.pos
  · exact_mod_cast Nat.nth_monotone Nat.infinite_setOf_prime hab

private theorem indexedPrimeReciprocal_not_summable :
    ¬ Summable indexedPrimeReciprocal := by
  intro hsum
  apply Nat.Primes.not_summable_one_div
  apply (hsum.comp_injective primeIndexEquiv.symm.injective).congr
  intro p
  simp [indexedPrimeReciprocal]

/-- At construction stage `k`, retain the multiples of `k + 1`. -/
private def stageReciprocal (k n : Nat) : Real :=
  if k + 1 ∣ n then indexedPrimeReciprocal n else 0

private theorem stageReciprocal_nonneg (k n : Nat) :
    0 <= stageReciprocal k n := by
  simp only [stageReciprocal]
  split_ifs
  · exact indexedPrimeReciprocal_nonneg n
  · exact le_rfl

private theorem stageReciprocal_not_summable (k : Nat) :
    ¬ Summable (stageReciprocal k) := by
  letI : NeZero (k + 1) := ⟨by omega⟩
  have hresidue : ¬ Summable
      ({n : Nat | (n : ZMod (k + 1)) = 0}.indicator indexedPrimeReciprocal) := by
    rw [summable_indicator_mod_iff indexedPrimeReciprocal_antitone
      (0 : ZMod (k + 1))]
    exact indexedPrimeReciprocal_not_summable
  rw [show stageReciprocal k =
      {n : Nat | (n : ZMod (k + 1)) = 0}.indicator indexedPrimeReciprocal by
    funext n
    have hiff : ((n : ZMod (k + 1)) = 0) ↔ k + 1 ∣ n :=
      ZMod.natCast_eq_zero_iff n (k + 1)
    by_cases hdiv : k + 1 ∣ n
    · have hzmod := hiff.mpr hdiv
      simp [stageReciprocal, Set.indicator, hdiv, hzmod]
    · have hzmod := mt hiff.mp hdiv
      simp [stageReciprocal, Set.indicator, hdiv, hzmod]]
  exact hresidue

private theorem stageBlock_exists (k start : Nat) :
    ∃ finish : Nat, start < finish ∧
      1 <= ∑ n ∈ Ico start finish, stageReciprocal k n := by
  have htendsto : Tendsto
      (fun finish : Nat => ∑ n ∈ range finish, stageReciprocal k n)
      atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (stageReciprocal_nonneg k)).mp (stageReciprocal_not_summable k)
  have hlarge := htendsto.eventually
    (eventually_ge_atTop ((∑ n ∈ range start, stageReciprocal k n) + 1))
  obtain ⟨finish, hfinish, hstart⟩ :=
    (hlarge.and (eventually_ge_atTop (start + 1))).exists
  refine ⟨finish, by omega, ?_⟩
  rw [← sum_range_add_sum_Ico (stageReciprocal k) (by omega : start <= finish)] at hfinish
  linarith

private noncomputable def blockFinish (k start : Nat) : Nat :=
  Nat.find (stageBlock_exists k start)

private theorem blockFinish_spec (k start : Nat) :
    start < blockFinish k start ∧
      1 <= ∑ n ∈ Ico start (blockFinish k start), stageReciprocal k n :=
  Nat.find_spec (stageBlock_exists k start)

private structure SparseState where
  cutoff : Nat
  chosen : Finset Nat

private def sparseStageStart (k : Nat) (state : SparseState) : Nat :=
  max state.cutoff (max ((k + 1) * state.chosen.card) (k + 1))

private noncomputable def nextSparseState (k : Nat) (state : SparseState) : SparseState :=
  let start := sparseStageStart k state
  let finish := blockFinish k start
  let block := (Ico start finish).filter fun n => k + 1 ∣ n
  ⟨finish, state.chosen ∪ block⟩

private noncomputable def sparseStates : Nat -> SparseState
  | 0 => ⟨0, ∅⟩
  | k + 1 => nextSparseState k (sparseStates k)

private theorem sparseStates_succ_cutoff (k : Nat) :
    (sparseStates (k + 1)).cutoff =
      blockFinish k (sparseStageStart k (sparseStates k)) := by
  rfl

private theorem sparseStates_succ_chosen (k : Nat) :
    (sparseStates (k + 1)).chosen =
      (sparseStates k).chosen ∪
        ((Ico (sparseStageStart k (sparseStates k))
          (blockFinish k (sparseStageStart k (sparseStates k)))).filter
            fun n => k + 1 ∣ n) := by
  rfl

private theorem cutoff_lt_succ (k : Nat) :
    (sparseStates k).cutoff < (sparseStates (k + 1)).cutoff := by
  rw [sparseStates_succ_cutoff]
  exact (le_max_left _ _).trans_lt
    (blockFinish_spec k (sparseStageStart k (sparseStates k))).1

private theorem cutoff_strictMono :
    StrictMono fun k => (sparseStates k).cutoff :=
  strictMono_nat_of_lt_succ cutoff_lt_succ

private theorem index_le_cutoff (k : Nat) :
    k <= (sparseStates k).cutoff := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => exact Nat.succ_le_of_lt (ih.trans_lt (cutoff_lt_succ k))

private theorem chosen_subset_succ (k : Nat) :
    (sparseStates k).chosen ⊆ (sparseStates (k + 1)).chosen := by
  rw [sparseStates_succ_chosen]
  exact subset_union_left

private theorem chosen_mono {k j : Nat} (hkj : k <= j) :
    (sparseStates k).chosen ⊆ (sparseStates j).chosen := by
  induction j, hkj using Nat.le_induction with
  | base => exact Subset.rfl
  | succ j _ ih => exact fun n hn => chosen_subset_succ j (ih hn)

private theorem chosen_lt_cutoff (k : Nat) {n : Nat}
    (hn : n ∈ (sparseStates k).chosen) :
    n < (sparseStates k).cutoff := by
  induction k with
  | zero => simp [sparseStates] at hn
  | succ k ih =>
      rw [sparseStates_succ_chosen] at hn
      rcases mem_union.mp hn with hold | hnew
      · exact (ih hold).trans (cutoff_lt_succ k)
      · exact (mem_Ico.mp (mem_filter.mp hnew).1).2

private theorem chosen_stable_below {k j n : Nat} (hkj : k <= j)
    (hn : n < (sparseStates k).cutoff) :
    (n ∈ (sparseStates j).chosen ↔ n ∈ (sparseStates k).chosen) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
  induction d with
  | zero => simp
  | succ d ih =>
      have ih' := ih (Nat.le_add_right k d)
      rw [Nat.add_succ, sparseStates_succ_chosen, mem_union]
      constructor
      · rintro (hold | hnew)
        · exact ih'.mp hold
        · have hstart := (mem_Ico.mp (mem_filter.mp hnew).1).1
          have hcutoff : (sparseStates k).cutoff <=
              (sparseStates (k + d)).cutoff :=
            cutoff_strictMono.monotone (Nat.le_add_right k d)
          have hstartCutoff : (sparseStates k).cutoff <=
              sparseStageStart (k + d) (sparseStates (k + d)) :=
            hcutoff.trans (le_max_left _ _)
          omega
      · intro hold
        exact Or.inl (ih'.mpr hold)

/-- The classically selected and accumulated sparse set of prime indices. -/
private def sparseIndexSupport : Set Nat :=
  {n | ∃ k, n ∈ (sparseStates k).chosen}

private noncomputable def sparseSupportCount (n : Nat) : Nat := by
  classical
  exact ((range n).filter fun i => i ∈ sparseIndexSupport).card

private theorem mem_sparseIndexSupport_iff_of_lt_cutoff (k n : Nat)
    (hn : n < (sparseStates k).cutoff) :
    n ∈ sparseIndexSupport ↔ n ∈ (sparseStates k).chosen := by
  constructor
  · rintro ⟨j, hj⟩
    rcases le_total j k with hjk | hkj
    · exact chosen_mono hjk hj
    · exact (chosen_stable_below hkj hn).mp hj
  · intro h
    exact ⟨k, h⟩

private theorem current_block_subset_support (k : Nat) :
    ∀ n ∈ ((Ico (sparseStageStart k (sparseStates k))
      (blockFinish k (sparseStageStart k (sparseStates k)))).filter
        fun n => k + 1 ∣ n : Finset Nat), n ∈ sparseIndexSupport := by
  intro n hn
  exact ⟨k + 1, by
    rw [sparseStates_succ_chosen]
    exact mem_union_right _ hn⟩

private theorem multiples_in_block_card_le (k start finish : Nat) :
    ((Ico start finish).filter fun n => k + 1 ∣ n).card <=
      finish / (k + 1) + 1 := by
  have hcard := card_le_card_of_injOn
    (s := (Ico start finish).filter fun n => k + 1 ∣ n)
    (t := range (finish / (k + 1) + 1))
    (fun n : Nat => n / (k + 1))
    (by
      intro n hn
      apply mem_range.mpr
      apply Nat.lt_succ_of_le
      exact Nat.div_le_div_right (le_of_lt (mem_Ico.mp (mem_filter.mp hn).1).2))
    (by
      intro a ha b hb hab
      have hda := (mem_filter.mp ha).2
      have hdb := (mem_filter.mp hb).2
      change a / (k + 1) = b / (k + 1) at hab
      calc
        a = (k + 1) * (a / (k + 1)) := (Nat.mul_div_cancel' hda).symm
        _ = (k + 1) * (b / (k + 1)) := by rw [hab]
        _ = b := Nat.mul_div_cancel' hdb)
  simpa only [card_range] using hcard

private theorem chosen_card_endpoint_bound (k : Nat) :
    (k + 1) * (sparseStates (k + 1)).chosen.card <=
      3 * (sparseStates (k + 1)).cutoff := by
  let start := sparseStageStart k (sparseStates k)
  let finish := blockFinish k start
  let block := (Ico start finish).filter fun n => k + 1 ∣ n
  have hcard : (sparseStates (k + 1)).chosen.card <=
      (sparseStates k).chosen.card + block.card := by
    rw [sparseStates_succ_chosen]
    change ((sparseStates k).chosen ∪ block).card <=
      (sparseStates k).chosen.card + block.card
    exact card_union_le _ _
  have hprevious : (k + 1) * (sparseStates k).chosen.card <= start := by
    simp only [start, sparseStageStart]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hstart_finish : start <= finish :=
    (blockFinish_spec k start).1.le
  have hmodulus_finish : k + 1 <= finish := by
    have : k + 1 <= start := by
      simp only [start, sparseStageStart]
      exact (le_max_right _ _).trans (le_max_right _ _)
    exact this.trans hstart_finish
  have hblock : block.card <= finish / (k + 1) + 1 :=
    multiples_in_block_card_le k start finish
  have hdiv : (k + 1) * (finish / (k + 1)) <= finish :=
    Nat.mul_div_le finish (k + 1)
  rw [sparseStates_succ_cutoff]
  change (k + 1) * (sparseStates (k + 1)).chosen.card <= 3 * finish
  have hmulCard : (k + 1) * (sparseStates (k + 1)).chosen.card <=
      (k + 1) * (sparseStates k).chosen.card + (k + 1) * block.card := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left (k + 1) hcard
  have hmulPrevious : (k + 1) * (sparseStates k).chosen.card <= finish :=
    hprevious.trans hstart_finish
  have hmulBlock : (k + 1) * block.card <= finish + (k + 1) := by
    have := Nat.mul_le_mul_left (k + 1) hblock
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  omega

private theorem support_count_in_gap (k n : Nat)
    (hcutoff : (sparseStates k).cutoff <= n)
    (hgap : n <= sparseStageStart k (sparseStates k))
    (hnext : n < (sparseStates (k + 1)).cutoff) :
    sparseSupportCount n = (sparseStates k).chosen.card := by
  classical
  unfold sparseSupportCount
  have heq : (range n).filter (fun i => i ∈ sparseIndexSupport) =
      (sparseStates k).chosen := by
    ext i
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hin, hsupport⟩
      have hnextChosen :=
        (mem_sparseIndexSupport_iff_of_lt_cutoff (k + 1) i
          (hin.trans hnext)).mp hsupport
      rw [sparseStates_succ_chosen] at hnextChosen
      rcases mem_union.mp hnextChosen with hold | hnew
      · exact hold
      · have hstart := (mem_Ico.mp (mem_filter.mp hnew).1).1
        omega
    · intro hchosen
      exact ⟨(chosen_lt_cutoff k hchosen).trans_le hcutoff,
        ⟨k, hchosen⟩⟩
  exact congrArg Finset.card heq

private theorem support_count_in_block_le (k n : Nat)
    (hnext : n < (sparseStates (k + 1)).cutoff) :
    sparseSupportCount n <=
      (sparseStates k).chosen.card + n / (k + 1) + 1 := by
  classical
  unfold sparseSupportCount
  let residue := (range n).filter fun i => k + 1 ∣ i
  have hsubset : ((range n).filter fun i => i ∈ sparseIndexSupport) ⊆
      (sparseStates k).chosen ∪ residue := by
    intro i hi
    have hirange := (mem_filter.mp hi).1
    have hsupport := (mem_filter.mp hi).2
    have hnextChosen :=
      (mem_sparseIndexSupport_iff_of_lt_cutoff (k + 1) i
        ((mem_range.mp hirange).trans hnext)).mp hsupport
    rw [sparseStates_succ_chosen] at hnextChosen
    rcases mem_union.mp hnextChosen with hold | hnew
    · exact mem_union_left _ hold
    · exact mem_union_right _ (mem_filter.mpr ⟨hirange, (mem_filter.mp hnew).2⟩)
  calc
    ((range n).filter fun i => i ∈ sparseIndexSupport).card <=
        ((sparseStates k).chosen ∪ residue).card := card_le_card hsubset
    _ <= (sparseStates k).chosen.card + residue.card := card_union_le _ _
    _ <= (sparseStates k).chosen.card + (n / (k + 1) + 1) := by
      gcongr
      simpa [residue, ← range_eq_Ico] using
        multiples_in_block_card_le k 0 n
    _ = (sparseStates k).chosen.card + n / (k + 1) + 1 := by omega

private theorem sparse_support_count_bound (K n : Nat) (hK : 0 < K)
    (hn : (sparseStates K).cutoff <= n) :
    K * sparseSupportCount n <= 3 * n := by
  classical
  have hexists : ∃ j, n < (sparseStates j).cutoff := by
    exact ⟨n + 1, lt_of_lt_of_le (Nat.lt_succ_self n) (index_le_cutoff (n + 1))⟩
  let j := Nat.find hexists
  have hj : n < (sparseStates j).cutoff := Nat.find_spec hexists
  have hjpos : 0 < j := by
    by_contra hjzero
    have : j = 0 := Nat.eq_zero_of_not_pos hjzero
    rw [this] at hj
    simp [sparseStates] at hj
  obtain ⟨k, hjk⟩ := Nat.exists_eq_succ_of_ne_zero hjpos.ne'
  rw [hjk] at hj
  have hkcutoff : (sparseStates k).cutoff <= n := by
    by_contra h
    have : n < (sparseStates k).cutoff := Nat.lt_of_not_ge h
    exact Nat.find_min hexists (by omega : k < j) this
  have hKk : K <= k := by
    by_contra h
    have hkleK : k + 1 <= K := by omega
    have hcutoffOrder := cutoff_strictMono.monotone hkleK
    exact (not_lt_of_ge (hcutoffOrder.trans hn)) hj
  by_cases hgap : n <= sparseStageStart k (sparseStates k)
  · rw [support_count_in_gap k n hkcutoff hgap hj]
    have hend := chosen_card_endpoint_bound (k - 1)
    have hkpos : 0 < k := lt_of_lt_of_le hK hKk
    have hkform : k - 1 + 1 = k := by omega
    rw [hkform] at hend
    have hKcard : K * (sparseStates k).chosen.card <=
        k * (sparseStates k).chosen.card := Nat.mul_le_mul_right _ hKk
    omega
  · have hstart : sparseStageStart k (sparseStates k) <= n := Nat.le_of_not_ge hgap
    have hcount := support_count_in_block_le k n hj
    have hprevious : (k + 1) * (sparseStates k).chosen.card <=
        sparseStageStart k (sparseStates k) := by
      exact (le_max_left _ _).trans (le_max_right _ _)
    have hdiv : (k + 1) * (n / (k + 1)) <= n := Nat.mul_div_le n (k + 1)
    have hmodulus : k + 1 <= n := by
      exact (le_max_right _ _).trans (le_max_right _ _) |>.trans hstart
    have hKsucc : K <= k + 1 := hKk.trans (Nat.le_succ k)
    have hmulCount : (k + 1) * sparseSupportCount n <=
        (k + 1) * (sparseStates k).chosen.card +
          (k + 1) * (n / (k + 1)) + (k + 1) := by
      have := Nat.mul_le_mul_left (k + 1) hcount
      simpa only [Nat.mul_add, Nat.mul_one] using this
    have hmulPrevious : (k + 1) * (sparseStates k).chosen.card <= n :=
      hprevious.trans hstart
    have hstageBound : (k + 1) * sparseSupportCount n <= 3 * n := by
      omega
    exact (Nat.mul_le_mul_right (sparseSupportCount n) hKsucc).trans hstageBound

private theorem sparseIndexSupport_density_zero :
    Tendsto
      (fun n : Nat => ((sparseSupportCount n : Real) / (n : Real)))
      atTop (nhds 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨K : Nat, hKreal : (3 : Real) / epsilon < K⟩ := exists_nat_gt (3 / epsilon)
  have hK : 0 < K := by
    have : (0 : Real) < K := lt_of_le_of_lt (by positivity : (0 : Real) <= 3 / epsilon) hKreal
    exact_mod_cast this
  refine ⟨(sparseStates K).cutoff, ?_⟩
  intro n hn
  have hbound := sparse_support_count_bound K n hK hn
  have hnpos : 0 < n := by
    have := index_le_cutoff K
    omega
  have hKpos : (0 : Real) < K := by exact_mod_cast hK
  have hnposReal : (0 : Real) < n := by exact_mod_cast hnpos
  have hratio :
      ((sparseSupportCount n : Real) / n) <=
        3 / K := by
    rw [div_le_div_iff₀ hnposReal hKpos]
    have hboundReal : (K : Real) * sparseSupportCount n <= 3 * (n : Real) := by
      exact_mod_cast hbound
    simpa [mul_comm] using hboundReal
  have hthree : (3 : Real) / K < epsilon := by
    rw [div_lt_iff₀ hKpos]
    rw [div_lt_iff₀ hepsilon] at hKreal
    simpa [mul_comm] using hKreal
  rw [Real.dist_eq, sub_zero, abs_of_nonneg]
  · exact hratio.trans_lt hthree
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem sparseIndexSupport_not_summable :
    ¬ Summable (sparseIndexSupport.indicator indexedPrimeReciprocal) := by
  classical
  intro hsum
  have htendsto : Tendsto
      (fun n : Nat => ∑ i ∈ range n, sparseIndexSupport.indicator indexedPrimeReciprocal i)
      atTop (nhds (∑' i, sparseIndexSupport.indicator indexedPrimeReciprocal i)) :=
    (hasSum_iff_tendsto_nat_of_nonneg
      (fun i => Set.indicator_nonneg (fun _ _ => indexedPrimeReciprocal_nonneg i) _) _).mp
        hsum.hasSum
  have hclose := htendsto.eventually
    (Metric.ball_mem_nhds _ (by norm_num : (0 : Real) < 1 / 3))
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hclose)
  let start := sparseStageStart N (sparseStates N)
  let finish := blockFinish N start
  have hstartN : N <= start := by
    exact (Nat.le_succ N).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hfinishN : N <= finish := hstartN.trans (blockFinish_spec N start).1.le
  have hstartClose := hN start hstartN
  have hfinishClose := hN finish hfinishN
  have hblockMass := (blockFinish_spec N start).2
  have hblockIdentity :
      (∑ i ∈ Ico start finish, sparseIndexSupport.indicator indexedPrimeReciprocal i) =
        ∑ i ∈ Ico start finish, stageReciprocal N i := by
    apply sum_congr rfl
    intro i hi
    by_cases hdiv : N + 1 ∣ i
    · rw [Set.indicator_of_mem, stageReciprocal, if_pos hdiv]
      exact current_block_subset_support N i (mem_filter.mpr ⟨hi, hdiv⟩)
    · rw [stageReciprocal, if_neg hdiv]
      have hnotmem : i ∉ sparseIndexSupport := by
        intro hmem
        have hilt : i < (sparseStates (N + 1)).cutoff := by
          rw [sparseStates_succ_cutoff]
          exact (mem_Ico.mp hi).2
        have hchosen := (mem_sparseIndexSupport_iff_of_lt_cutoff (N + 1) i
          hilt).mp hmem
        rw [sparseStates_succ_chosen] at hchosen
        rcases mem_union.mp hchosen with hold | hnew
        · have holdlt := chosen_lt_cutoff N hold
          have histart := (mem_Ico.mp hi).1
          exact (not_lt_of_ge ((le_max_left _ _).trans histart)) holdlt
        · exact hdiv (mem_filter.mp hnew).2
      simp [Set.indicator, hnotmem]
  have hpartial :
      (∑ i ∈ Ico start finish, sparseIndexSupport.indicator indexedPrimeReciprocal i) =
        (∑ i ∈ range finish, sparseIndexSupport.indicator indexedPrimeReciprocal i) -
          ∑ i ∈ range start, sparseIndexSupport.indicator indexedPrimeReciprocal i := by
    rw [sum_Ico_eq_sub _ (blockFinish_spec N start).1.le]
  have hstartAbs : abs
      ((∑ i ∈ range start, sparseIndexSupport.indicator indexedPrimeReciprocal i) -
        ∑' i, sparseIndexSupport.indicator indexedPrimeReciprocal i) < 1 / 3 := by
    simpa [Real.dist_eq] using hstartClose
  have hfinishAbs : abs
      ((∑ i ∈ range finish, sparseIndexSupport.indicator indexedPrimeReciprocal i) -
        ∑' i, sparseIndexSupport.indicator indexedPrimeReciprocal i) < 1 / 3 := by
    simpa [Real.dist_eq] using hfinishClose
  rw [← hblockIdentity, hpartial] at hblockMass
  have : abs
      ((∑ i ∈ range finish, sparseIndexSupport.indicator indexedPrimeReciprocal i) -
        ∑ i ∈ range start, sparseIndexSupport.indicator indexedPrimeReciprocal i) < 2 / 3 := by
    calc
      abs ((∑ i ∈ range finish, sparseIndexSupport.indicator indexedPrimeReciprocal i) -
          ∑ i ∈ range start, sparseIndexSupport.indicator indexedPrimeReciprocal i) =
          abs (((∑ i ∈ range finish, sparseIndexSupport.indicator indexedPrimeReciprocal i) -
            ∑' i, sparseIndexSupport.indicator indexedPrimeReciprocal i) -
            ((∑ i ∈ range start, sparseIndexSupport.indicator indexedPrimeReciprocal i) -
              ∑' i, sparseIndexSupport.indicator indexedPrimeReciprocal i)) := by ring_nf
      _ <= abs ((∑ i ∈ range finish, sparseIndexSupport.indicator indexedPrimeReciprocal i) -
            ∑' i, sparseIndexSupport.indicator indexedPrimeReciprocal i) +
          abs ((∑ i ∈ range start, sparseIndexSupport.indicator indexedPrimeReciprocal i) -
            ∑' i, sparseIndexSupport.indicator indexedPrimeReciprocal i) := abs_sub _ _
      _ < 2 / 3 := by linarith
  have hnonneg : 0 <=
      (∑ i ∈ range finish, sparseIndexSupport.indicator indexedPrimeReciprocal i) -
        ∑ i ∈ range start, sparseIndexSupport.indicator indexedPrimeReciprocal i := by
    exact hblockMass.trans' (by norm_num)
  rw [abs_of_nonneg hnonneg] at this
  linarith

/-- Proposition 235.1's prime subset, classically selected from the sparse index blocks above. -/
def sparseReciprocalPrimeSupport : Set Nat.Primes :=
  primeIndexEquiv '' sparseIndexSupport

private theorem indexed_mem_sparse_prime_support (n : Nat) :
    primeIndexEquiv n ∈ sparseReciprocalPrimeSupport ↔ n ∈ sparseIndexSupport := by
  constructor
  · rintro ⟨j, hj, heq⟩
    exact primeIndexEquiv.injective heq ▸ hj
  · intro hn
    exact ⟨n, hn, rfl⟩

private noncomputable def sparseSupportEquiv :
    sparseIndexSupport ≃ sparseReciprocalPrimeSupport where
  toFun n := ⟨primeIndexEquiv n.1,
    (indexed_mem_sparse_prime_support n.1).mpr n.2⟩
  invFun p := ⟨primeIndexEquiv.symm p.1,
    (indexed_mem_sparse_prime_support (primeIndexEquiv.symm p.1)).mp (by
      simpa using p.2)⟩
  left_inv n := by
    apply Subtype.ext
    exact primeIndexEquiv.symm_apply_apply n.1
  right_inv p := by
    apply Subtype.ext
    exact primeIndexEquiv.apply_symm_apply p.1

/-- Source lines 13815--13821: the constructed prime subset has relative density zero. -/
theorem sparse_reciprocal_prime_support_density_zero :
    Tendsto (relativePrimeCountingRatio sparseReciprocalPrimeSupport) atTop (nhds 0) := by
  classical
  apply sparseIndexSupport_density_zero.congr'
  filter_upwards [] with n
  have hfinset :
      (range n).filter (fun i => primeIndexEquiv i ∈ sparseReciprocalPrimeSupport) =
        (range n).filter (fun i => i ∈ sparseIndexSupport) := by
    ext i
    simp [indexed_mem_sparse_prime_support]
  have hcard := congrArg Finset.card hfinset
  rw [relativePrimeCountingRatio]
  unfold sparseSupportCount
  rw [hcard]

/-- Source lines 13815--13825: the actual reciprocal-prime mass on the same subset diverges. -/
theorem sparse_reciprocal_prime_support_not_summable :
    ¬ Summable (fun p : sparseReciprocalPrimeSupport => (1 : Real) / p.1.1) := by
  intro hsum
  apply sparseIndexSupport_not_summable
  have hsubtype : Summable (fun n : sparseIndexSupport =>
      indexedPrimeReciprocal n.1) := by
    apply (hsum.comp_injective sparseSupportEquiv.injective).congr
    intro n
    rfl
  exact summable_subtype_iff_indicator.mp hsubtype

/-- FPOD Proposition 235.1 (source lines 13813--13834). There is one prime
subset with zero relative density and divergent reciprocal mass. Moreover, under
the singularity/divergence equivalence in source Theorem 233.1 (lines 13702--13710),
any prime evidence asymptotic to `1 / p` on that subset still makes the two
transcript laws mutually singular. -/
theorem zero_density_divergent_reciprocal_prime_set :
    ∃ S : Set Nat.Primes,
      Tendsto (relativePrimeCountingRatio S) atTop (nhds 0) ∧
      ¬ Summable (fun p : S => (1 : Real) / p.1.1) ∧
      ∀ {Transcript : Type} [MeasurableSpace Transcript]
        (evidence : Nat.Primes -> Real) (productP productQ : Measure Transcript),
        (productP ⟂ₘ productQ ↔ ¬ Summable evidence) ->
        ((fun p : S => evidence p.1) =Θ[cofinite]
          (fun p : S => (1 : Real) / p.1.1)) ->
        productP ⟂ₘ productQ := by
  refine ⟨sparseReciprocalPrimeSupport,
    sparse_reciprocal_prime_support_density_zero,
    sparse_reciprocal_prime_support_not_summable, ?_⟩
  intro Transcript _ evidence productP productQ hK htheta
  apply hK.mpr
  intro hevidence
  apply sparse_reciprocal_prime_support_not_summable
  exact htheta.summable_iff.mp (hevidence.subtype sparseReciprocalPrimeSupport)

#print axioms zero_density_divergent_reciprocal_prime_set

/-- Reverse probe for A1: the public proposition exposes zero relative density. -/
private theorem reverse_probe_a1_density_zero :
    ∃ S : Set Nat.Primes,
      Tendsto (relativePrimeCountingRatio S) atTop (nhds 0) := by
  obtain ⟨S, hdensity, _, _⟩ :=
    zero_density_divergent_reciprocal_prime_set
  exact ⟨S, hdensity⟩

/-- Reverse probe for A2: the public proposition exposes divergent reciprocal mass. -/
private theorem reverse_probe_a2_reciprocal_divergence :
    ∃ S : Set Nat.Primes,
      ¬ Summable (fun p : S => (1 : Real) / p.1.1) := by
  obtain ⟨S, _, hdivergence, _⟩ :=
    zero_density_divergent_reciprocal_prime_set
  exact ⟨S, hdivergence⟩

/-- Reverse probe for A3: the public proposition separately exposes conditional completion. -/
private theorem reverse_probe_a3_conditional_completion :
    ∃ S : Set Nat.Primes,
    ∀ {Transcript : Type} [MeasurableSpace Transcript]
      (evidence : Nat.Primes -> Real) (productP productQ : Measure Transcript),
      (productP ⟂ₘ productQ ↔ ¬ Summable evidence) ->
      ((fun p : S => evidence p.1) =Θ[cofinite]
        (fun p : S => (1 : Real) / p.1.1)) ->
      productP ⟂ₘ productQ := by
  obtain ⟨S, _, _, hcompletion⟩ :=
    zero_density_divergent_reciprocal_prime_set
  exact ⟨S, hcompletion⟩

/-- Trivialization probe: no finite prime set can replace the theorem's support. -/
private theorem finite_prime_support_reciprocal_summable
    (S : Set Nat.Primes) (hS : S.Finite) :
    Summable (fun p : S => (1 : Real) / p.1.1) := by
  letI : Finite S := hS.to_subtype
  letI := Fintype.ofFinite S
  exact (hasSum_fintype _).summable

/-- The selected support is simultaneously infinite and zero-density. -/
private theorem sparse_reciprocal_prime_support_infinite_and_sparse :
    sparseReciprocalPrimeSupport.Infinite ∧
      Tendsto (relativePrimeCountingRatio sparseReciprocalPrimeSupport)
        atTop (nhds 0) := by
  refine ⟨?_, sparse_reciprocal_prime_support_density_zero⟩
  intro hfinite
  exact sparse_reciprocal_prime_support_not_summable
    (finite_prime_support_reciprocal_summable sparseReciprocalPrimeSupport hfinite)

end

end D5.S3.Analytic.ZetaEntropyPlane.ZeroDensityReciprocalPrimeSet

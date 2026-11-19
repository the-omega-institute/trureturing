/- GID: D5/S3/Combinatorics/Partitions/RookClassCandidate
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/RookClassCandidate
   mirror-E: none(waiver:registered-universal-candidate)
   anchors: []
   utility: none
   digest: The registered weighted root sum equals the genuine native rook-class count at every common padding. -/

import D5.S3.Combinatorics.Partitions.RookRootIndex
import D5.S3.Combinatorics.Partitions.RookAugmentedLevels

/-! The registered formula is proved on the native cell-subset rook class.
    Its root family is identified with that same class using actual level totals,
    their singleton law, area preservation and exact root multiplicities.
    No literature factorization or rook-number preservation is assumed as an axiom.

    New public theorems have proof_shape: content after expanding the new helpers:
    rookEquivalent_iff_seedRoots uses the native completion bijection and
    falling-polynomial coefficient recovery; universal_formula uses the reversible
    native-class/root-family identification. These are symbolic family results,
    not bounded enumeration, a numeric certificate or a certified instance.
    Escape registration remains unfinished under issue #31465. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Partitions.RookClassCandidate

open D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
open D5.S3.Combinatorics.Partitions.FerrersLevelCounting
open D5.S3.Combinatorics.Partitions.RookClassNative
open D5.S3.Combinatorics.Partitions.RookRootIndex
open scoped BigOperators

private theorem operator_data (m : ℕ) (b : PositiveColumns) :
    (∀ x ∈ lOperator m b, 0 < x) ∧
      ∀ p, columnLevel m b p = (lOperator m b).reverse.getD p 0 := by
  exact (operatorFiberEquiv m (lOperator m b) ⟨b,rfl⟩).property

private theorem operator_length_le_area (m : ℕ) (hm : 0 < m) (b : PositiveColumns) :
    (lOperator m b).length ≤ area b := by
  let c := lOperator m b
  have hs := operator_data m b
  change c.length ≤ area b
  by_cases hc : c.length = 0
  · omega
  let p := c.length - 1
  have hp : p < c.reverse.length := by simp only [List.length_reverse]; omega
  have hpos : 0 < columnLevel m b p := by
    rw [hs.2, List.getD_eq_getElem _ _ hp]
    exact hs.1 _ (List.mem_reverse.mp (List.getElem_mem hp))
  have hex : ∃ j : Fin m,
      0 < Fintype.card {i : Fin b.val.length // m*p+j.val < b.val[i.val]} := by
    by_contra! hh
    have hz : columnLevel m b p = 0 := Finset.sum_eq_zero (fun j _ => by
      exact Nat.eq_zero_of_le_zero (hh j))
    omega
  obtain ⟨j,hj⟩ := hex
  obtain ⟨⟨i,hi⟩⟩ := Fintype.card_pos_iff.mp hj
  have hsum : b.val[i.val] ≤ area b := List.le_sum_of_mem (List.getElem_mem i.isLt)
  have hmul : p ≤ m*p := by
    simpa only [one_mul] using Nat.mul_le_mul_right p (show 1 ≤ m by omega)
  dsimp only [p] at *
  omega

/-- Auxiliary columns use the ordered top-down l-operator, including its empty
    extension. They are not arbitrary original-board candidates. -/
def sourcePadding (m N : ℕ) (b : PositiveColumns) : List ℕ :=
  List.replicate (N-(lOperator m b).length) 0 ++ lOperator m b

/-- Source root multiset at the fixed common length. -/
def seedRoots (m N : ℕ) (b : PositiveColumns) (i : Fin N) : ℤ :=
  (m : ℤ) * (i.val : ℤ) - ((sourcePadding m N b).getD i.val 0 : ℤ)

/-- Fully evaluated Barrese weight, with precisely the supplier's reversal,
    bottom-level bound, nonpositive guard and empty-list base case. -/
def weight (m : ℕ) (c : List ℕ) : ℤ := by
  classical
  exact if (∀ x ∈ c, 0 < x) then
    count (m-1) (c.reverse.getD 0 0) c.reverse
      ⟨c.reverse.getD 0 0, Nat.lt_succ_self _⟩ else 0

/-- The exact registered candidate: a finite sum over distinct admissible roots,
    evaluated with the Gaussian transfer recurrence, not by searching boards. -/
def Q (m N : ℕ) (b : PositiveColumns) : ℤ :=
  ∑ a : ↥(indices m (seedRoots m N b)), weight m (board m a).val

/-- Ordinary class size. The separate rookClass_finite theorem proves the
    carrier finite before any use of Nat.card. -/
def K (m : ℕ) (b : PositiveColumns) : ℕ := Nat.card (RookClass m b)

/-- The exact registered all-parameter proposition, proved by universal_formula. -/
def UniversalFormula : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (b : PositiveColumns) (N : ℕ), area b + 1 ≤ N →
    (K m b : ℤ) = Q m N b

private theorem operator_fiber_finite (m : ℕ) (hm : 0 < m) (c : List ℕ) :
    Finite {b : PositiveColumns // lOperator m b = c} := by
  classical
  by_cases hc : ∀ x ∈ c, 0 < x
  · obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    let e := ((operatorFiberEquiv (r+1) c).trans (sourceShapeEquiv (r+1) c hc)).trans
      (D5.S3.Combinatorics.Partitions.BarreseAllWidths.normalizedPaddingEquiv r c.reverse)
    exact Finite.of_equiv _ e.symm
  · haveI : IsEmpty {b : PositiveColumns // lOperator m b = c} := ⟨by
      rintro ⟨b,hb⟩
      apply hc
      rw [← hb]
      exact (operator_data m b).1⟩
    infer_instance

/-- The actual normalized source shapes whose l-data occur in the root index.
    The native identification is proved without changing this carrier. -/
abbrev RootFamily (m : ℕ) {N : ℕ} (z : Fin N → ℤ) :=
  {b : PositiveColumns // ∃ a : ↥(indices m z), lOperator m b = (board m a).val}

/-- Forgetting the index gives a bijection because reconstruction is injective.
    Every fiber contains the same actual normalized source shapes as its image. -/
def rootFiberEquiv (m : ℕ) {N : ℕ} (z : Fin N → ℤ) :
    ((a : ↥(indices m z)) × {b : PositiveColumns // lOperator m b = (board m a).val}) ≃
      RootFamily m z := by
  let f : ((a : ↥(indices m z)) × {b : PositiveColumns // lOperator m b = (board m a).val}) →
      RootFamily m z := fun x => ⟨x.2.val,⟨x.1,x.2.property⟩⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨a,b⟩ ⟨a',b'⟩ h
    have hb : b.val = b'.val := congrArg Subtype.val h
    have ha : a = a' := board_injective m z (Subtype.ext (by
      rw [← b.property, ← b'.property, hb]))
    subst a'
    have hb' : b = b' := Subtype.ext hb
    subst b'
    rfl
  · rintro ⟨b,⟨a,ha⟩⟩
    exact ⟨⟨a,⟨b,ha⟩⟩,rfl⟩

/-- The union over all distinct root indices is finite and its ordinary finite
    cardinality is the evaluated weight sum. This is the fiber-assembly interface;
    identifying the union with a native rook class remains a separate theorem. -/
theorem rootFamily_count (m : ℕ) (hm : 0 < m) {N : ℕ} (z : Fin N → ℤ) :
    Finite (RootFamily m z) ∧
      (Nat.card (RootFamily m z) : ℤ) =
        ∑ a : ↥(indices m z), weight m (board m a).val := by
  classical
  letI : ∀ a : ↥(indices m z), Finite {b : PositiveColumns // lOperator m b = (board m a).val} :=
    fun a => operator_fiber_finite m hm (board m a).val
  have hf : Finite (RootFamily m z) := Finite.of_equiv _ (rootFiberEquiv m z)
  refine ⟨hf, ?_⟩
  rw [← Nat.card_congr (rootFiberEquiv m z), Nat.card_sigma, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun a _ => lOperator_count m hm (board m a).val)

/-- All registered lengths accommodate the actual ordered l-data, with a leading
    zero. This holds for arbitrary nonsingleton inputs and for the empty board. -/
theorem candidate_padding (m : ℕ) (hm : 0 < m) (b : PositiveColumns) (N : ℕ)
    (hN : area b + 1 ≤ N) :
    (lOperator m b).length < N ∧ (sourcePadding m N b).length = N ∧
      (sourcePadding m N b).head? = some 0 ∧
      ∀ i : Fin N, i.val = 0 → seedRoots m N b i = 0 := by
  have hl := operator_length_le_area m hm b
  have ht : (lOperator m b).length < N := by omega
  have hp : N-(lOperator m b).length = (N-(lOperator m b).length-1)+1 := by omega
  have hh : (sourcePadding m N b).head? = some 0 := by
    rw [sourcePadding, hp, List.replicate_succ, List.cons_append]
    rfl
  refine ⟨ht, ?_, hh, ?_⟩
  · simp only [sourcePadding, List.length_append, List.length_replicate]
    omega
  · intro i hi
    rw [seedRoots, hi, Int.natCast_zero, mul_zero]
    have hget : (sourcePadding m N b).getD 0 0 = 0 := by
      rw [sourcePadding, hp, List.replicate_succ, List.cons_append]
      rfl
    rw [hget]
    rfl

open D5.S3.Combinatorics.Partitions.RookAugmentedLevels
open D5.S3.Combinatorics.Partitions.RookRootCriterion
open D5.S3.Combinatorics.Partitions.BarreseSourceNormalization (column_anti)

private theorem sourcePadding_levels (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (hN : area b + 1 ≤ N) (i : Fin N) :
    (sourcePadding m N b).getD i.val 0 = columnLevel m b (N-1-i.val) := by
  have hl := operator_length_le_area m hm b
  rw [(operator_data m b).2]
  unfold sourcePadding
  by_cases hi : i.val < N-(lOperator m b).length
  · rw [List.getD_append _ _ _ _ (by simpa using hi)]
    have hz : (List.replicate (N-(lOperator m b).length) 0).getD i.val 0 = 0 := by simp
    rw [hz, List.getD_eq_default _ _ (by simp only [List.length_reverse]; omega)]
  · rw [List.getD_append_right _ _ _ _ (by simpa using (show N-(lOperator m b).length ≤ i.val by omega))]
    rw [List.getD_reverse _ (by have := i.isLt; omega)]
    simp only [List.length_replicate]
    congr 1
    have := i.isLt
    omega

private theorem seedRoots_levels (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (hN : area b + 1 ≤ N) : seedRoots m N b = levelRoots m N b := by
  funext i
  rw [seedRoots, levelRoots, sourcePadding_levels m N hm b hN i]

/-- Exact native rook equivalence is the multiset equality of the registered
    source roots, at every common registered padding. -/
theorem rookEquivalent_iff_seedRoots (m N : ℕ) (hm : 0 < m)
    (a b : PositiveColumns) (ha : area a + 1 ≤ N) (hb : area b + 1 ≤ N) :
    RookEquivalent m a b ↔
      (List.ofFn (seedRoots m N a)).Perm (List.ofFn (seedRoots m N b)) := by
  rw [rookEquivalent_iff_levelPolynomial m N hm a b ha hb,
    levelPolynomial_eq_iff_roots m N hm a b,
    seedRoots_levels m N hm a ha, seedRoots_levels m N hm b hb]

private theorem sourcePadding_monotone (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (hN : area b + 1 ≤ N) :
    Monotone (fun i : Fin N => (sourcePadding m N b).getD i.val 0) := by
  intro i j hij
  dsimp only
  rw [sourcePadding_levels m N hm b hN i, sourcePadding_levels m N hm b hN j]
  apply column_anti m b
  have hh : i.val ≤ j.val := hij
  omega

private theorem seed_admissible (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (hN : area b + 1 ≤ N) : Admissible m (seedRoots m N b) := by
  have hh (i : Fin N) : heights m (seedRoots m N b) i =
      ((sourcePadding m N b).getD i.val 0 : ℤ) := by
    simp [heights, seedRoots]
  refine ⟨(candidate_padding m hm b N hN).2.2.2, ?_, ?_, ?_⟩
  · intro i
    rw [hh]
    exact Nat.cast_nonneg _
  · intro i j hij
    rw [hh, hh]
    exact_mod_cast sourcePadding_monotone m N hm b hN hij
  · have hs := level_totals_singleton m N hm b
    have hs' : SingletonColumns m
        (fun i : Fin N => (sourcePadding m N b).getD i.val 0) := by
      simpa only [sourcePadding_levels m N hm b hN] using hs
    have hr := (rootFloorCriterion_iff_singleton m hm _
      (sourcePadding_monotone m N hm b hN)).mpr hs'
    exact hr

private theorem sourcePadding_eq_ofFn (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (hN : area b + 1 ≤ N) : sourcePadding m N b =
      List.ofFn (fun i : Fin N => columnLevel m b (N-1-i.val)) := by
  apply List.ext_getElem
    ((candidate_padding m hm b N hN).2.1.trans (List.length_ofFn.symm))
  intro n hn hn'
  rw [← List.getD_eq_getElem _ _ hn, List.getElem_ofFn]
  exact sourcePadding_levels m N hm b hN ⟨n,by simpa only [List.length_ofFn] using hn'⟩

private theorem sourcePadding_sum (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (hN : area b + 1 ≤ N) : (sourcePadding m N b).sum = area b := by
  rw [sourcePadding_eq_ofFn m N hm b hN, Fin.sum_ofFn]
  exact level_totals_sum m N hm b hN

private theorem operator_sum (m : ℕ) (hm : 0 < m) (b : PositiveColumns) :
    (lOperator m b).sum = area b := by
  simpa only [sourcePadding, List.sum_append, List.sum_replicate, nsmul_zero, zero_add] using
    sourcePadding_sum m (area b+1) hm b (by omega)

open D5.S3.Combinatorics.Partitions.RookRootIndex
  (paddedRoots_board reconstruction_area mem_rootPermutations_iff index_spec)

private theorem board_seed (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (hN : area b + 1 ≤ N) (a : ↥(indices m (seedRoots m N b)))
    (ha : a.val = seedRoots m N b) : (board m a).val = lOperator m b := by
  have hd : decode m a.val = fun i : Fin N => (sourcePadding m N b).getD i.val 0 := by
    funext i
    rw [ha]
    simp [decode, heights, seedRoots]
  have hp := (candidate_padding m hm b N hN).2.1
  have hlist : List.ofFn (fun i : Fin N => (sourcePadding m N b).getD i.val 0) =
      sourcePadding m N b := by
    apply List.ext_getElem (by simpa only [List.length_ofFn] using hp.symm)
    intro n hn hn'
    rw [List.getElem_ofFn]
    exact List.getD_eq_getElem _ _ hn'
  change (List.ofFn (decode m a.val)).filter (fun x => x != 0) = _
  rw [hd,hlist]
  simp only [sourcePadding, List.filter_append, List.filter_replicate, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, List.nil_append]
  apply List.filter_eq_self.mpr
  intro x hx
  exact bne_iff_ne.mpr (Nat.ne_of_gt ((operator_data m b).1 x hx))

private theorem rootFamily_iff_native (m N : ℕ) (hm : 0 < m) (b : PositiveColumns)
    (hN : area b + 1 ≤ N) (a : PositiveColumns) :
    RookEquivalent m a b ↔ ∃ j : ↥(indices m (seedRoots m N b)),
      lOperator m a = (board m j).val := by
  classical
  constructor
  · intro h
    have ha : area a = area b := by simpa only [rookCount_one] using h 1
    have haN : area a + 1 ≤ N := by omega
    have hp := (rookEquivalent_iff_seedRoots m N hm a b haN hN).mp h
    let j : ↥(indices m (seedRoots m N b)) := ⟨seedRoots m N a,
      Finset.mem_filter.mpr ⟨(mem_rootPermutations_iff _ _).mpr hp,
        seed_admissible m N hm a haN⟩⟩
    refine ⟨j, ?_⟩
    exact (board_seed m N hm a haN
      ⟨j.val,Finset.mem_filter.mpr ⟨(mem_rootPermutations_iff _ _).mpr (List.Perm.refl _),
        seed_admissible m N hm a haN⟩⟩ rfl).symm
  · rintro ⟨j,hj⟩
    have harea : area (board m j) = area b := by
      have h := reconstruction_area m
        (fun i : Fin N => (sourcePadding m N b).getD i.val 0) j
      have hs : (∑ i : Fin N, (sourcePadding m N b).getD i.val 0) = area b := by
        simp_rw [sourcePadding_levels m N hm b hN]
        exact level_totals_sum m N hm b hN
      exact h.trans hs
    have ha : area a = area b := by
      rw [← operator_sum m hm a, hj]
      exact harea
    have hr : seedRoots m N a = j.val := by
      unfold seedRoots sourcePadding
      rw [hj]
      change paddedRoots m N (board m j) = j.val
      exact paddedRoots_board m j
    apply (rookEquivalent_iff_seedRoots m N hm a b (by omega) hN).mpr
    rw [hr]
    exact (index_spec m (seedRoots m N b) j).1

/-- The entire registered formula on the genuine native rook class, including
    empty and nonsingleton boards and every registered common padding. -/
theorem universal_formula : UniversalFormula := by
  intro m hm b N hN
  let e : RookClass m b ≃ RootFamily m (seedRoots m N b) :=
    Equiv.subtypeEquivRight (rootFamily_iff_native m N hm b hN)
  rw [K, Nat.card_congr e]
  exact (rootFamily_count m hm (seedRoots m N b)).2

end D5.S3.Combinatorics.Partitions.RookClassCandidate

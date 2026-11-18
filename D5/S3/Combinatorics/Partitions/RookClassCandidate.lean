/- GID: D5/S3/Combinatorics/Partitions/RookClassCandidate
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/RookClassCandidate
   mirror-E: none(waiver:registered-universal-candidate)
   anchors: []
   utility: none
   digest: The registered finite weighted root sum has a well-defined common source padding. -/

import D5.S3.Combinatorics.Partitions.RookRootIndex

/-! The formula is the registered candidate, not a theorem of rook equivalence.
    Padding of the supplier's actual l-operator is proved without assuming
    preservation of rook numbers or importing a paper's factorization as an axiom. -/

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

/-- The all-parameter target remains an explicit proposition. No proof of this
    declaration is supplied by the padding or root-index theorems. -/
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
    Equality of this carrier with the native rook class is not assumed here. -/
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

end D5.S3.Combinatorics.Partitions.RookClassCandidate

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
      exact Nat.eq_zero_of_not_pos (hh j))
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

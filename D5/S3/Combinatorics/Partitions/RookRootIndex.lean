/- GID: D5/S3/Combinatorics/Partitions/RookRootIndex
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/RookRootIndex
   mirror-E: none(waiver:distinct-root-reconstruction)
   anchors: []
   utility: none
   digest: Distinct admissible root sequences reconstruct unique normalized singleton boards. -/

import D5.S3.Combinatorics.Partitions.RookRootCriterion
import Mathlib.Data.List.FinRange

/-! Finite root-multiset enumeration and exact removal of leading zero columns.
    The connection to equality of native rook numbers is a separate obligation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Partitions.RookRootIndex

open D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
open D5.S3.Combinatorics.Partitions.RookClassNative
open D5.S3.Combinatorics.Partitions.RookRootCriterion
open scoped BigOperators

/-- The explicit integer column heights before nonnegative conversion. -/
def heights (m : ℕ) {N : ℕ} (a : Fin N → ℤ) (i : Fin N) : ℤ :=
  (m : ℤ) * (i.val : ℤ) - a i

/-- The registered conditions, with the first coordinate stated without a
    partial Fin constructor. All uses in the candidate have N > 0. -/
def Admissible (m : ℕ) {N : ℕ} (a : Fin N → ℤ) : Prop :=
  (∀ i, i.val = 0 → a i = 0) ∧ (∀ i, 0 ≤ heights m a i) ∧
    Monotone (heights m a) ∧ RootFloorCriterion m a

/-- Enumerate root sequences and deduplicate equal entries before filtering.
    The enumeration is over root permutations, never over the board class. -/
def rootPermutations {N : ℕ} (z : Fin N → ℤ) : Finset (Fin N → ℤ) :=
  (List.ofFn z).permutations.toFinset.image (fun l i => l.getD i.val 0)

/-- The exact finite source-root filter. -/
def indices (m : ℕ) {N : ℕ} (z : Fin N → ℤ) : Finset (Fin N → ℤ) := by
  classical
  exact (rootPermutations z).filter (Admissible m)

private theorem ofFn_getD {N : ℕ} (l : List ℤ) (hl : l.length = N) :
    List.ofFn (fun i : Fin N => l.getD i.val 0) = l := by
  subst N
  simpa only [List.getD_eq_getElem] using (List.ofFn_getElem l)

private theorem mem_rootPermutations_iff {N : ℕ} (z a : Fin N → ℤ) :
    a ∈ rootPermutations z ↔ (List.ofFn a).Perm (List.ofFn z) := by
  constructor
  · intro h
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp h
    have hp := List.mem_permutations.mp (List.mem_toFinset.mp hl)
    rw [ofFn_getD l (by simpa using hp.length_eq)]
    exact hp
  · intro h
    refine Finset.mem_image.mpr ⟨List.ofFn a,
      List.mem_toFinset.mpr (List.mem_permutations.mpr h), ?_⟩
    funext i
    simp [List.getD_eq_getElem]

private theorem index_spec (m : ℕ) {N : ℕ} (z : Fin N → ℤ)
    (a : ↥(indices m z)) :
    (List.ofFn a.val).Perm (List.ofFn z) ∧ Admissible m a.val := by
  obtain ⟨hp,ha⟩ := Finset.mem_filter.mp a.property
  exact ⟨(mem_rootPermutations_iff z a.val).mp hp,ha⟩

/-- The nonnegative reconstructed padded column tuple. -/
def decode (m : ℕ) {N : ℕ} (a : Fin N → ℤ) (i : Fin N) : ℕ :=
  (heights m a i).toNat

private theorem decode_spec (m : ℕ) {N : ℕ} (a : Fin N → ℤ)
    (ha : Admissible m a) (i : Fin N) : (decode m a i : ℤ) = heights m a i :=
  Int.toNat_of_nonneg (ha.2.1 i)

private theorem decode_monotone (m : ℕ) {N : ℕ} (a : Fin N → ℤ)
    (ha : Admissible m a) : Monotone (decode m a) := by
  intro i j hij
  exact Int.toNat_le_toNat (ha.2.2.1 hij)

private theorem split_zero_prefix (l : List ℕ) (hl : l.SortedLE) :
    List.replicate (l.length - (l.filter (fun x => x != 0)).length) 0 ++
      l.filter (fun x => x != 0) = l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hpair := List.pairwise_cons.mp hl.pairwise
    by_cases hx : x = 0
    · subst x
      have ht := ih hpair.2.sortedLE
      have hlen : (xs.filter (fun x => x != 0)).length ≤ xs.length := List.length_filter_le _ _
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        List.length_cons]
      have he : xs.length + 1 - (xs.filter (fun x => x != 0)).length =
          (xs.length - (xs.filter (fun x => x != 0)).length) + 1 := by omega
      rw [he, List.replicate_succ, List.cons_append, ht]
    · have hp : ∀ y ∈ x::xs, (y != 0) = true := by
        intro y hy
        have hy' : 0 < y := by
          rcases List.mem_cons.mp hy with rfl | hy
          · omega
          · have := hpair.1 y hy; omega
        simpa using Nat.ne_of_gt hy'
      rw [List.filter_eq_self.mpr hp]
      simp

/-- Normalize by removing exactly the zero prefix. The sorted-column hypothesis
    ensures that no positive column is removed or reordered. -/
def board (m : ℕ) {N : ℕ} {z : Fin N → ℤ} (a : ↥(indices m z)) : PositiveColumns :=
  ⟨(List.ofFn (decode m a.val)).filter (fun x => x != 0),
    ((decode_monotone m a.val (index_spec m z a).2).sortedLE_ofFn.pairwise.filter _).sortedLE,
    by
      intro x hx
      have hx' := (List.mem_filter.mp hx).2
      simp only [bne_iff_ne] at hx'
      omega⟩

private theorem pad_board (m : ℕ) {N : ℕ} {z : Fin N → ℤ} (a : ↥(indices m z)) :
    pad N (board m a) = List.ofFn (decode m a.val) := by
  have hh := split_zero_prefix (List.ofFn (decode m a.val))
    ((decode_monotone m a.val (index_spec m z a).2).sortedLE_ofFn)
  simpa only [List.length_ofFn] using hh

/-- Root entries at the fixed common padding, with zero extension only to make
    the total function usable outside its intended length-bound hypotheses. -/
def paddedRoots (m N : ℕ) (b : PositiveColumns) (i : Fin N) : ℤ :=
  (m : ℤ) * (i.val : ℤ) - ((pad N b).getD i.val 0 : ℤ)

private theorem paddedRoots_board (m : ℕ) {N : ℕ} {z : Fin N → ℤ}
    (a : ↥(indices m z)) : paddedRoots m N (board m a) = a.val := by
  funext i
  rw [paddedRoots, pad_board]
  simp only [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn]
  rw [decode_spec m a.val (index_spec m z a).2]
  simp [heights]

/-- Fixed-length reconstruction cannot count one normalized board twice, even
    with repeated roots, leading zeros, or an empty positive-column list. -/
theorem board_injective (m : ℕ) {N : ℕ} (z : Fin N → ℤ) :
    Function.Injective (board m (z := z)) := by
  intro a b h
  apply Subtype.ext
  have he := congrArg (paddedRoots m N) h
  simpa only [paddedRoots_board] using he

/-- The reconstructed padded tuple satisfies the geometric singleton law and
    recovers the entire original root sequence. -/
theorem reconstruction (m : ℕ) (hm : 0 < m) {N : ℕ} (z : Fin N → ℤ)
    (a : ↥(indices m z)) :
    pad N (board m a) = List.ofFn (decode m a.val) ∧
      paddedRoots m N (board m a) = a.val ∧ SingletonColumns m (decode m a.val) := by
  have ha := (index_spec m z a).2
  refine ⟨pad_board m a, paddedRoots_board m a, ?_⟩
  apply (rootFloorCriterion_iff_singleton m hm (decode m a.val)
    (decode_monotone m a.val ha)).mp
  have hr : root m (decode m a.val) = a.val := by
    funext i
    rw [root, decode_spec m a.val ha]
    simp [heights]
  rw [hr]
  exact ha.2.2.2

end D5.S3.Combinatorics.Partitions.RookRootIndex

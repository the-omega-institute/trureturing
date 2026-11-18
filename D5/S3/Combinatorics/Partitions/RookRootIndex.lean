/- GID: D5/S3/Combinatorics/Partitions/RookRootIndex
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/RookRootIndex
   mirror-E: none(waiver:distinct-root-reconstruction)
   anchors: []
   utility: none
   digest: Distinct admissible root sequences reconstruct unique normalized singleton boards. -/

import D5.S3.Combinatorics.Partitions.RookRootCriterion
import Mathlib.Data.List.FinRange
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.GroupAction.Quotient

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
  calc
    _ = List.ofFn (fun i : Fin l.length => l[i.val]) := by
      congr 1
      funext i
      exact List.getD_eq_getElem l 0 i.isLt
    _ = l := List.ofFn_getElem

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
  classical
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
  simpa only [pad, board, List.length_ofFn] using hh

/-- Root entries at the fixed common padding, with zero extension only to make
    the total function usable outside its intended length-bound hypotheses. -/
def paddedRoots (m N : ℕ) (b : PositiveColumns) (i : Fin N) : ℤ :=
  (m : ℤ) * (i.val : ℤ) - ((pad N b).getD i.val 0 : ℤ)

private theorem paddedRoots_board (m : ℕ) {N : ℕ} {z : Fin N → ℤ}
    (a : ↥(indices m z)) : paddedRoots m N (board m a) = a.val := by
  funext i
  rw [paddedRoots, pad_board]
  have hi : i.val < (List.ofFn (decode m a.val)).length := by
    simpa only [List.length_ofFn] using i.isLt
  rw [List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
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

private theorem board_area (m : ℕ) {N : ℕ} {z : Fin N → ℤ}
    (a : ↥(indices m z)) : (area (board m a) : ℤ) =
      ∑ i : Fin N, heights m a.val i := by
  have hp := congrArg List.sum (pad_board m a)
  have hs : area (board m a) = ∑ i : Fin N, decode m a.val i := by
    simpa [pad, area, Fin.sum_ofFn] using hp
  rw [hs, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun i _ => decode_spec m a.val (index_spec m z a).2 i)

private theorem reconstruction_area (m : ℕ) {N : ℕ} (d : Fin N → ℕ)
    (a : ↥(indices m (root m d))) : area (board m a) = ∑ i, d i := by
  have hp := (index_spec m (root m d) a).1.sum_eq
  have hs : (∑ i : Fin N, a.val i) = ∑ i : Fin N, root m d i := by
    simpa only [Fin.sum_ofFn] using hp
  have hh : (area (board m a) : ℤ) = ∑ i : Fin N, (d i : ℤ) := by
    rw [board_area]
    simp only [heights, Finset.sum_sub_distrib, hs, root]
    ring
  exact_mod_cast hh

private theorem fiber_card {N : ℕ} (f : Fin N → ℤ) (t : ℤ) :
    Fintype.card {i : Fin N // f i = t} = (List.ofFn f).count t := by
  classical
  rw [Fintype.card_subtype]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.ofFn_succ, List.count_cons, Finset.card_filter]
    rw [Fin.sum_univ_succ]
    have ht := ih (fun i => f i.succ)
    rw [Finset.card_filter] at ht
    rw [ht]
    by_cases h : f 0 = t
    · simp only [h, BEq.rfl, ↓reduceIte, Nat.add_comm]
    · have h' : (f 0 == t) = false := beq_eq_false_iff_ne.mpr h
      simp only [h, h', Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero]

private theorem perm_iff_orbit {N : ℕ} (z a : Fin N → ℤ) :
    (List.ofFn a).Perm (List.ofFn z) ↔
      a ∈ MulAction.orbit (Equiv.Perm (Fin N))ᵈᵐᵃ z := by
  classical
  constructor
  · intro h
    let e (t : ℤ) : {i : Fin N // a i = t} ≃ {i : Fin N // z i = t} :=
      Fintype.equivOfCardEq (by rw [fiber_card, fiber_card]; exact h.count_eq t)
    let σ : Equiv.Perm (Fin N) := Equiv.ofFiberEquiv e
    refine MulAction.mem_orbit_iff.mpr ⟨DomMulAct.mk σ, ?_⟩
    funext i
    exact Equiv.ofFiberEquiv_map e i
  · rintro ⟨σ,rfl⟩
    exact (DomMulAct.mk.symm σ).ofFn_comp_perm z

/-- The multiplicities count values, never labels assigned to equal roots. -/
def multiplicityFactor {N : ℕ} (z : Fin N → ℤ) : ℕ :=
  ∏ t ∈ Finset.univ.image z, (Fintype.card {i : Fin N // z i = t}).factorial

private theorem permutations_card {N : ℕ} (z : Fin N → ℤ) :
    (rootPermutations z).card = N.factorial / multiplicityFactor z := by
  classical
  let G := (Equiv.Perm (Fin N))ᵈᵐᵃ
  letI : Fintype G := Fintype.ofEquiv (Equiv.Perm (Fin N)) DomMulAct.mk
  let O := MulAction.orbit G z
  letI : Fintype O := (Finite.finite_mulAction_orbit (M := G) z).fintype
  let e : ↥(rootPermutations z) ≃ O :=
    Equiv.subtypeEquivRight (fun a => (mem_rootPermutations_iff z a).trans (perm_iff_orbit z a))
  have hs : Fintype.card (MulAction.stabilizer G z) = multiplicityFactor z := by
    let es : {g : Equiv.Perm (Fin N) // z ∘ g = z} ≃ MulAction.stabilizer G z :=
      Equiv.subtypeEquiv DomMulAct.mk (fun _ => Iff.rfl)
    rw [← Fintype.card_congr es]
    exact DomMulAct.stabilizer_card' z
  have hg : Fintype.card G = N.factorial := by
    rw [← Fintype.card_congr (DomMulAct.mk : Equiv.Perm (Fin N) ≃ G), Fintype.card_perm]
    simp
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G z
  rw [hs,hg] at h
  have hp : 0 < multiplicityFactor z := by
    unfold multiplicityFactor
    exact Finset.prod_pos (fun _ _ => Nat.factorial_pos _)
  rw [← Fintype.card_coe, Fintype.card_congr e, ← h, Nat.mul_div_cancel _ hp]

/-- A family-level index specification: the registered finite multinomial bound,
    unique normalized representatives, geometric singleton law, and area are
    simultaneous properties of the very same reconstruction. -/
theorem index_family (m : ℕ) (hm : 0 < m) {N : ℕ} (d : Fin N → ℕ) :
    (indices m (root m d)).card ≤ N.factorial / multiplicityFactor (root m d) ∧
      Function.Injective (board m (z := root m d)) ∧
      ∀ a : ↥(indices m (root m d)),
        pad N (board m a) = List.ofFn (decode m a.val) ∧
          paddedRoots m N (board m a) = a.val ∧
          SingletonColumns m (decode m a.val) ∧ area (board m a) = ∑ i, d i := by
  classical
  refine ⟨?_, board_injective m (root m d), ?_⟩
  · rw [← permutations_card]
    exact Finset.card_filter_le _ _
  · intro a
    have hr := reconstruction m hm (root m d) a
    exact ⟨hr.1,hr.2.1,hr.2.2,reconstruction_area m d a⟩

end D5.S3.Combinatorics.Partitions.RookRootIndex

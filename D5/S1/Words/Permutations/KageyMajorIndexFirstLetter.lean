/- GID: D5/S1/Words/Permutations/KageyMajorIndexFirstLetter
   generality: I
   mirror-B: D5/B/S1/Words/Permutations/KageyMajorIndexFirstLetter
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Major-index first-letter expectations have the monic rational form of Conjecture 5.2. -/

/-
admission_basis: open-problem-resolution (#19720; Proved)
result: proof_shape: content; escape_witness: countPoly_eval_descent.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21383.
The first-letter expression is inlined. It equals (PSW.word π).headD 0;
the one-line-word owner is in S3, so its literal expression is used here.
The descent-family expression uses the published D5/S0/Asymptotics/GeneratingFunctions/KotesovecA022629.partitions owner directly; no local duplicate is declared.
Direct frozen dependencies: D5/S0/Asymptotics/GeneratingFunctions/KotesovecA022629.partitions (statement_id: sha256:9fb96c80099db857b0d24325a86f6a13e2c9d4161d0815bb3bd8f9c4390193ca), D5/S1/Words/Patterns/Separable/CutFactorization.descentAt (statement_id: sha256:28fc9e09665283c7f64320e2add25f00f9d9e71189e2353b8109d36dd003a2f9).
-/

import D5.S1.Words.Permutations.OrderedBlockAllocations
import D5.S1.Words.Patterns.Separable.CutFactorization
import D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fintype.Lattice
open scoped Classical

/-! Binding conventions for P. Kagey, "Expected value of letters of permutations with a given number of k-cycles",
arXiv:2112.05281v1, Section 5.2: permutations `π ∈ S_n` in one-line notation, the major index
`maj(π) = ∑_{π(i) > π(i+1)} i`, and Conjecture 5.2: "For fixed k > 0 and n ≥ k, E[π(1) | π ∈ S_n, maj(π) = k] satisfies
a rational function in n that is 1/(k + 1) times the quotient of a monic degree-(k + 1) polynomial by a monic degree-k
polynomial". -/

namespace D5.S1.Words.Permutations.KageyMajorIndexFirstLetter

open D5.S1.Words.Patterns.Separable.CutFactorization (descentAt)

/-- The major index `maj(π) = ∑_{i : π(i) > π(i+1)} i` over 1-based positions `i`; `descentAt π i` is the D5 descent
indicator at 0-based position `i`. -/
def maj {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  ∑ i : Fin n, (i.val + 1) * descentAt π i

/-- `#{π ∈ S_n : maj(π) = k}`. -/
def count (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun π : Equiv.Perm (Fin n) => maj π = k).card

/-- `E[π(1) | π ∈ S_n, maj(π) = k]`. -/
def E (n k : ℕ) : ℚ :=
  (∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) => maj π = k), ((if h : 0 < n then (π ⟨0, h⟩).val + 1 else 0 : ℕ) : ℚ)) / (count n k : ℚ)

/-- Conjecture 5.2: for each `k > 0` there are monic `P` of degree `k + 1` and `Q` of degree `k` with
`E[π(1) | π ∈ S_n, maj(π) = k] = P(n) / ((k + 1) Q(n))` for every `n ≥ k` at which the conditioning set is nonempty. -/
def claim : Prop :=
  ∀ k : ℕ, 0 < k → ∃ P Q : Polynomial ℚ, P.Monic ∧ Q.Monic ∧ P.natDegree = k + 1 ∧ Q.natDegree = k ∧
    ∀ n : ℕ, k ≤ n → count n k ≠ 0 → E n k = P.eval (n : ℚ) / ((k + 1 : ℚ) * Q.eval (n : ℚ))

end D5.S1.Words.Permutations.KageyMajorIndexFirstLetter

namespace D5.S1.Words.Permutations.KageyMajorIndexFirstLetter
namespace Blocks
open D5.S1.Words.Permutations.OrderedBlockAllocations
open D5.S1.Words.Patterns.Separable.CutFactorization (descentAt)
private def cutLabel (U : Finset ℕ) {n : ℕ} (i : Fin n) : Fin (U.card + 1) :=
  ⟨(U.filter (· ≤ i.val)).card, by
    have := Finset.card_filter_le U (fun u => u ≤ i.val)
    omega⟩
private theorem cutLabel_eq_iff {n : ℕ} (U : Finset ℕ) (a b : Fin n) (hab : a ≤ b) :
    cutLabel U a = cutLabel U b ↔ ∀ u ∈ U, a.val < u → b.val < u := by
  have hsub : U.filter (· ≤ a.val) ⊆ U.filter (· ≤ b.val) := by
    intro u hu
    simp only [Finset.mem_filter] at hu ⊢
    exact ⟨hu.1, le_trans hu.2 hab⟩
  constructor
  · intro h u hu hau
    have hc : (U.filter (· ≤ a.val)).card = (U.filter (· ≤ b.val)).card :=
      congrArg Fin.val h
    have he := Finset.eq_of_subset_of_card_le hsub hc.ge
    by_contra hbu
    have : u ∈ U.filter (· ≤ a.val) := by rw [he]; exact Finset.mem_filter.mpr ⟨hu, le_of_not_gt hbu⟩
    exact (not_le_of_gt hau) (Finset.mem_filter.mp this).2
  · intro h
    apply Fin.ext
    apply congrArg Finset.card
    apply Finset.Subset.antisymm hsub
    intro u hu
    simp only [Finset.mem_filter] at hu ⊢
    refine ⟨hu.1, ?_⟩
    by_contra hua
    exact (not_lt_of_ge hu.2) (h u hu.1 (lt_of_not_ge hua))
private theorem cutLabel_adjacent {n : ℕ} (U : Finset ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    cutLabel U i = cutLabel U ⟨i.val + 1, hi⟩ ↔ i.val + 1 ∉ U := by
  rw [cutLabel_eq_iff U i ⟨i.val + 1, hi⟩ (by exact Nat.le_add_right _ _)]
  change (∀ u ∈ U, i.val < u → i.val + 1 < u) ↔ i.val + 1 ∉ U
  constructor
  · intro h hu
    have := h (i.val + 1) hu (by omega)
    omega
  · intro h u hu hlt
    by_contra hle
    have : u = i.val + 1 := by omega
    exact h (this ▸ hu)
private theorem increasingOnBlocks_iff_descents {n : ℕ} (U : Finset ℕ)
    (π : Equiv.Perm (Fin n)) :
    IncreasingOnBlocks (cutLabel U) π ↔
      ∀ i : Fin n, descentAt π i ≠ 0 → i.val + 1 ∈ U := by
  constructor
  · intro h i hd
    by_contra hcut
    unfold descentAt at hd
    split at hd
    · rename_i hi
      have hlt := h i ⟨i.val + 1, hi⟩ ((cutLabel_adjacent U i hi).mpr hcut) (by exact Nat.lt_succ_self _)
      simp only [not_lt_of_gt hlt, ↓reduceIte, ne_eq, not_true_eq_false] at hd
    · simp at hd
  · intro h a b hlabel hab
    have hcuts := (cutLabel_eq_iff U a b hab.le).mp hlabel
    let f : ℕ → Fin n := fun t => if ht : t < n then π ⟨t, ht⟩ else π a
    have hmono : MonotoneOn f (Set.Icc a.val b.val) := by
      apply monotoneOn_of_le_succ Set.ordConnected_Icc
      intro t _ ht htNext
      have htn : t < n := ht.2.trans_lt b.isLt
      have hsn : t + 1 < n := htNext.2.trans_lt b.isLt
      have hat : a.val ≤ t := ht.1
      have htb : t + 1 ≤ b.val := htNext.2
      have hnotcut : t + 1 ∉ U := by
        intro hm
        have := hcuts (t + 1) hm (by omega)
        omega
      have hd : descentAt π ⟨t, htn⟩ = 0 := by
        by_contra hh
        exact hnotcut (h ⟨t, htn⟩ hh)
      have hnext : π ⟨t, htn⟩ ≤ π ⟨t + 1, hsn⟩ := by
        unfold descentAt at hd
        simp only [hsn, ↓reduceDIte] at hd
        split at hd
        · simp at hd
        · rename_i hlt
          exact le_of_not_gt hlt
      simpa only [f, Order.succ_eq_add_one, dite_eq_left htn, dite_eq_left hsn] using hnext
    have habπ : π a ≤ π b := by
      have hm := hmono (show a.val ∈ Set.Icc a.val b.val from ⟨le_rfl, hab.le⟩)
        (show b.val ∈ Set.Icc a.val b.val from ⟨hab.le, le_rfl⟩) hab.le
      simpa only [f, dite_eq_left a.isLt, dite_eq_left b.isLt] using hm
    exact lt_of_le_of_ne habπ (fun he => (ne_of_lt hab) (π.injective he))

end Blocks
end D5.S1.Words.Permutations.KageyMajorIndexFirstLetter

namespace D5.S1.Words.Permutations.KageyMajorIndexFirstLetter.Blocks
open D5.S1.Words.Permutations.OrderedBlockAllocations
open Finset

end D5.S1.Words.Permutations.KageyMajorIndexFirstLetter.Blocks

namespace D5.S1.Words.Permutations.KageyMajorIndexFirstLetter.Blocks
open D5.S1.Words.Permutations.OrderedBlockAllocations
open Finset
private theorem cutLabel_last_iff {n : ℕ} (U : Finset ℕ) (i : Fin n) :
    cutLabel U i = (Fin.last U.card) ↔ (U.sup id) ≤ i.val := by
  constructor
  · intro h
    have hc : (U.filter (· ≤ i.val)).card = U.card := congrArg Fin.val h
    have he := eq_of_subset_of_card_le (filter_subset (· ≤ i.val) U) hc.ge
    change U.sup id ≤ i.val
    apply Finset.sup_le
    intro u hu
    have : u ∈ U.filter (· ≤ i.val) := he.symm ▸ hu
    exact (mem_filter.mp this).2
  · intro h
    apply Fin.ext
    change (U.filter (· ≤ i.val)).card = U.card
    congr 1
    apply filter_eq_self.mpr
    intro u hu
    exact (le_sup (f := id) hu).trans h
private noncomputable def tailFiberEquiv {n : ℕ} (U : Finset ℕ) (hm : (U.sup id) ≤ n) :
    {aFiber // (@cutLabel U n) aFiber = ((Fin.last U.card))} ≃ Fin (n - (U.sup id)) where
  toFun a := ⟨a.val.val - (U.sup id), by
    have ha := (cutLabel_last_iff U a.val).mp a.2
    have hn := a.val.isLt
    omega⟩
  invFun a := ⟨⟨a.val + (U.sup id), by have := a.isLt; omega⟩,
    (cutLabel_last_iff U _).mpr (show (U.sup id) ≤ a.val + (U.sup id) from Nat.le_add_left _ _)⟩
  left_inv a := by
    apply Subtype.ext
    apply Fin.ext
    have ha := (cutLabel_last_iff U a.val).mp a.2
    simp only
    omega
  right_inv a := by apply Fin.ext; simp
private theorem tailFiber_card {n : ℕ} (U : Finset ℕ) (hm : (U.sup id) ≤ n) :
    Fintype.card ({aFiber // (@cutLabel U n) aFiber = ((Fin.last U.card))}) = n - (U.sup id) := by
  simpa using Fintype.card_congr (tailFiberEquiv U hm)
private noncomputable def prefixFiberEquiv {n : ℕ} (U : Finset ℕ) (hm : (U.sup id) ≤ n)
    (j : Fin (U.card + 1)) (hj : j ≠ (Fin.last U.card)) :
    {aFiber // (@cutLabel U n) aFiber = j} ≃ {aFiber // (@cutLabel U ((U.sup id))) aFiber = j} where
  toFun a := ⟨⟨a.val.val, by
    by_contra h
    have hl := (cutLabel_last_iff U a.val).mpr (le_of_not_gt h)
    exact hj (a.2.symm.trans hl)⟩, a.2⟩
  invFun a := ⟨⟨a.val.val, a.val.isLt.trans_le hm⟩, a.2⟩
  left_inv a := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv a := by apply Subtype.ext; apply Fin.ext; rfl
private noncomputable def blockDenom (U : Finset ℕ) : ℕ :=
  ∏ j ∈ (univ : Finset (Fin (U.card + 1))).erase ((Fin.last U.card)),
    (Fintype.card ({aFiber // (@cutLabel U ((U.sup id))) aFiber = j})).factorial
private theorem blockDenom_ne_zero (U : Finset ℕ) : blockDenom U ≠ 0 := by
  exact prod_ne_zero_iff.mpr (fun _ _ => Nat.factorial_ne_zero _)
private theorem cut_block_factorial {n : ℕ} (U : Finset ℕ) (hm : (U.sup id) ≤ n) :
    Fintype.card (Allocation (@cutLabel U n)) * blockDenom U * (n - (U.sup id)).factorial =
      n.factorial := by
  have h := allocation_card_factorial (@cutLabel U n)
  have hp : (∏ j : Fin (U.card + 1), (Fintype.card ({aFiber // (@cutLabel U n) aFiber = j})).factorial) =
      blockDenom U * (n - (U.sup id)).factorial := by
    rw [← prod_erase_mul _ _ (mem_univ ((Fin.last U.card))), tailFiber_card U hm]
    congr 1
    apply prod_congr rfl
    intro j hj
    rw [Fintype.card_congr (prefixFiberEquiv U hm j (mem_erase.mp hj).1)]
  rw [hp, Fintype.card_fin] at h
  convert! h using 1 <;> simp only [mul_assoc] <;> congr!

end D5.S1.Words.Permutations.KageyMajorIndexFirstLetter.Blocks

namespace D5.S1.Words.Permutations.KageyMajorIndexFirstLetter.Blocks
open D5.S1.Words.Permutations.OrderedBlockAllocations
open Finset Polynomial
private noncomputable def countPoly (U : Finset ℕ) : Polynomial ℚ :=
  C ((blockDenom U : ℚ)⁻¹) * descPochhammer ℚ ((U.sup id))
private theorem countPoly_eval {n : ℕ} (U : Finset ℕ) (hm : (U.sup id) ≤ n) :
    (countPoly U).eval (n : ℚ) = Fintype.card (Allocation (@cutLabel U n)) := by
  rw [countPoly, eval_mul, eval_C, descPochhammer_eval_eq_descFactorial]
  have h := cut_block_factorial U hm
  have hf := Nat.factorial_mul_descFactorial hm
  have he : Fintype.card (Allocation (@cutLabel U n)) * blockDenom U =
      n.descFactorial ((U.sup id)) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (n - (U.sup id)))
    calc
      _ = n.factorial := h
      _ = _ := by simpa only [mul_comm] using hf.symm
  have heQ : (Fintype.card (Allocation (@cutLabel U n)) : ℚ) * (blockDenom U : ℚ) =
      (n.descFactorial ((U.sup id)) : ℚ) := by exact_mod_cast he
  have hden : (blockDenom U : ℚ) ≠ 0 := by exact_mod_cast blockDenom_ne_zero U
  rw [← heQ]
  field_simp
private theorem countPoly_natDegree (U : Finset ℕ) : (countPoly U).natDegree = (U.sup id) := by
  rw [countPoly, natDegree_C_mul, descPochhammer_natDegree]
  exact inv_ne_zero (by exact_mod_cast blockDenom_ne_zero U)
private theorem countPoly_leadingCoeff (U : Finset ℕ) :
    (countPoly U).leadingCoeff = (blockDenom U : ℚ)⁻¹ := by
  rw [countPoly, leadingCoeff_mul, leadingCoeff_C, (monic_descPochhammer ℚ ((U.sup id))).leadingCoeff, mul_one]
private theorem cutLabel_zero_iff {n : ℕ} (U : Finset ℕ) (hU : U.Nonempty) (i : Fin n) :
    cutLabel U i = 0 ↔ i.val < U.min' hU := by
  change (⟨(U.filter (· ≤ i.val)).card, _⟩ : Fin (U.card + 1)) = 0 ↔ _
  rw [Fin.ext_iff]
  change (U.filter (· ≤ i.val)).card = 0 ↔ _
  rw [card_eq_zero, filter_eq_empty_iff]
  constructor
  · intro h
    have := h (min'_mem U hU)
    omega
  · intro h u hu
    have := min'_le U u hu
    omega
private noncomputable def firstFiberEquiv {n : ℕ} (U : Finset ℕ) (hU : U.Nonempty)
    (hm : (U.sup id) ≤ n) :
    {aFiber // (@cutLabel U n) aFiber = 0} ≃ Fin (U.min' hU) where
  toFun a := ⟨a.val.val, (cutLabel_zero_iff U hU a.val).mp a.2⟩
  invFun a := ⟨⟨a.val, by
    have hmin : U.min' hU ≤ (U.sup id) := le_sup (f := id) (min'_mem U hU)
    exact a.isLt.trans_le (hmin.trans hm)⟩,
    (cutLabel_zero_iff U hU _).mpr a.isLt⟩
  left_inv a := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv a := by apply Fin.ext; rfl
private theorem cutLabel_first_zero {n : ℕ} (hn : 0 < n) (U : Finset ℕ)
    (hpos : ∀ u ∈ U, 0 < u) : cutLabel U (⟨0, hn⟩ : Fin n) = 0 := by
  apply Fin.ext
  change (U.filter (· ≤ 0)).card = 0
  rw [card_eq_zero, filter_eq_empty_iff]
  intro u hu
  exact not_le_of_gt (hpos u hu)
private noncomputable def weightedPoly (U : Finset ℕ) : Polynomial ℚ :=
  if h : U.Nonempty then C (((U.min' h + 1 : ℕ) : ℚ)⁻¹) * (X + 1) * countPoly U else 1
private theorem weightedPoly_eval_nonempty {n : ℕ} (hn : 0 < n) (U : Finset ℕ)
    (hU : U.Nonempty) (hpos : ∀ u ∈ U, 0 < u) (hm : (U.sup id) ≤ n) :
    (weightedPoly U).eval (n : ℚ) =
      ∑ p : {π : Equiv.Perm (Fin n) // IncreasingOnBlocks (@cutLabel U n) π}, ((if h : 0 < n then (p.1 ⟨0, h⟩).val + 1 else 0 : ℕ) : ℚ) := by
  have hw := weighted_increasing_blocks hn (@cutLabel U n)
  rw [cutLabel_first_zero hn U hpos,
    Fintype.card_congr (firstFiberEquiv U hU hm)] at hw
  simp only [Fintype.card_fin] at hw
  rw [weightedPoly, dif_pos hU, eval_mul, eval_mul, eval_C, eval_add, eval_X, eval_one,
    countPoly_eval U hm]
  have hc := card_increasingOnBlocks (@cutLabel U n)
  rw [hc] at hw
  have hd : (((U.min' hU + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  apply (mul_left_cancel₀ hd)
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  convert! hw.symm using 1 <;> try simp only []
  all_goals congr!

end D5.S1.Words.Permutations.KageyMajorIndexFirstLetter.Blocks

namespace D5.S1.Words.Permutations.KageyMajorIndexFirstLetter.Blocks
open D5.S1.Words.Permutations.OrderedBlockAllocations
open Finset Polynomial
@[simp] private theorem blockDenom_empty : blockDenom ∅ = 1 := by
  unfold blockDenom
  apply prod_eq_one
  intro j hj
  have hjne := (mem_erase.mp hj).1
  apply (hjne ?_).elim
  apply Fin.ext
  have hjlt := j.isLt
  simp only [Finset.card_empty, Nat.zero_add] at hjlt
  change j.val = 0
  omega
@[simp] private theorem countPoly_empty : countPoly ∅ = 1 := by
  simp [countPoly]
@[simp] private theorem weightedPoly_empty : weightedPoly ∅ = 1 := by
  simp [weightedPoly]
private theorem weightedPoly_eval {n : ℕ} (hn : 0 < n) (U : Finset ℕ)
    (hpos : ∀ u ∈ U, 0 < u) (hm : (U.sup id) ≤ n) :
    (weightedPoly U).eval (n : ℚ) =
      ∑ p : {π : Equiv.Perm (Fin n) // IncreasingOnBlocks (@cutLabel U n) π}, ((if h : 0 < n then (p.1 ⟨0, h⟩).val + 1 else 0 : ℕ) : ℚ) := by
  rcases U.eq_empty_or_nonempty with rfl | hU
  · have hw := weighted_increasing_blocks hn (@cutLabel ∅ n)
    have hc : Fintype.card ({aFiber // (@cutLabel ∅ n) aFiber = (cutLabel ∅ ⟨0, hn⟩)}) = n := by
      simp [cutLabel, Fintype.card_subtype]
    rw [hc] at hw
    have hcardQ : (Fintype.card {π : Equiv.Perm (Fin n) // IncreasingOnBlocks (@cutLabel ∅ n) π} : ℚ) = 1 := by
      rw [card_increasingOnBlocks (@cutLabel ∅ n)]
      have he := countPoly_eval (n := n) ∅ (by simp)
      have he' : (Fintype.card (Allocation (@cutLabel ∅ n)) : ℚ) = 1 := by
        simpa using he.symm
      convert! he' using 1 <;> congr!
    rw [hcardQ] at hw
    simp only [Nat.cast_add, Nat.cast_one] at hw
    have hnQ : (n + 1 : ℚ) ≠ 0 := Nat.cast_add_one_ne_zero n
    have he := (mul_left_cancel₀ hnQ) hw
    simpa only [weightedPoly_empty, eval_one] using he.symm
  · exact weightedPoly_eval_nonempty hn U hU hpos hm
private theorem weightedPoly_natDegree_nonempty (U : Finset ℕ) (hU : U.Nonempty) :
    (weightedPoly U).natDegree = (U.sup id) + 1 := by
  have hc : (((U.min' hU + 1 : ℕ) : ℚ)⁻¹) ≠ 0 := by positivity
  rw [weightedPoly, dif_pos hU, mul_assoc, natDegree_C_mul hc,
    natDegree_mul (by exact (monic_X_add_C 1).ne_zero)
      (by
        intro hzero
        have hz := congrArg Polynomial.leadingCoeff hzero
        rw [countPoly_leadingCoeff, leadingCoeff_zero] at hz
        exact (inv_ne_zero (by exact_mod_cast blockDenom_ne_zero U)) hz)]
  rw [countPoly_natDegree]
  simp [natDegree_X_add_C, add_comm]

end D5.S1.Words.Permutations.KageyMajorIndexFirstLetter.Blocks

namespace D5.S1.Words.Permutations.KageyMajorIndexFirstLetter
open Finset
/-- Weighted Boolean-lattice inversion, with exact and contained finite descent sets. -/
private theorem exact_descent_inclusion_exclusion {α ι : Type} [Fintype α] [DecidableEq α]
    [DecidableEq ι] (D : α → Finset ι) (s : Finset ι) (w : α → ℚ) :
    (∑ a ∈ univ.filter (fun a => D a = s), w a) =
      ∑ U ∈ s.powerset, (-1 : ℚ) ^ (s.card - U.card) *
        ∑ a ∈ univ.filter (fun a => D a ⊆ U), w a := by
  let V : ι → Finset α := fun i => univ.filter (fun a => i ∉ D a)
  let w' : α → ℚ := fun a => if D a ⊆ s then w a else 0
  have ie := inclusion_exclusion_sum_inf_compl s V w'
  have hl : (∑ a ∈ s.inf (fun i => (V i)ᶜ), w' a) =
      ∑ a ∈ univ.filter (fun a => D a = s), w a := by
    change (∑ a ∈ s.inf (fun i => (V i)ᶜ), if D a ⊆ s then w a else 0) = _
    rw [← sum_filter]
    apply sum_congr
    · ext a
      simp only [mem_filter, Finset.mem_inf, mem_compl, V, mem_univ, true_and, not_not]
      exact ⟨fun h => h.2.antisymm h.1, fun h => ⟨h ▸ (fun _ hi => hi), h ▸ (fun _ hi => hi)⟩⟩
    · intro a ha; rfl
  have hr (t : Finset ι) : (∑ a ∈ t.inf V, w' a) =
      ∑ a ∈ univ.filter (fun a => D a ⊆ s \ t), w a := by
    change (∑ a ∈ t.inf V, if D a ⊆ s then w a else 0) = _
    rw [← sum_filter]
    apply sum_congr
    · ext a
      simp only [mem_filter, Finset.mem_inf, V, mem_univ, true_and]
      constructor
      · rintro ⟨ht, hs⟩ i hi
        exact mem_sdiff.mpr ⟨hs hi, fun hit => ht i hit hi⟩
      · intro h
        refine ⟨?_, ?_⟩
        · intro i hit hi; exact (mem_sdiff.mp (h hi)).2 hit
        · intro i hi; exact (mem_sdiff.mp (h hi)).1
    · intro a ha; rfl
  rw [hl] at ie
  simp_rw [hr, zsmul_eq_mul] at ie
  rw [ie]
  apply sum_bij (fun t ht => s \ t)
  · intro t ht
    exact mem_powerset.mpr sdiff_subset
  · intro t ht u hu htu
    have ht' := mem_powerset.mp ht
    have hu' := mem_powerset.mp hu
    have := congrArg (fun x => s \ x) htu
    simpa [Finset.sdiff_sdiff_eq_self ht', Finset.sdiff_sdiff_eq_self hu'] using this
  · intro U hU
    refine ⟨s \ U, mem_powerset.mpr sdiff_subset, ?_⟩
    exact Finset.sdiff_sdiff_eq_self (mem_powerset.mp hU)
  · intro t ht
    have ht' := mem_powerset.mp ht
    have hc : s.card - (s \ t).card = t.card := by
      rw [card_sdiff_of_subset ht']
      have := card_le_card ht'
      omega
    rw [hc]
    norm_cast

end D5.S1.Words.Permutations.KageyMajorIndexFirstLetter

namespace D5.S1.Words.Permutations.KageyMajorIndexFirstLetter
open Finset
open D5.S1.Words.Patterns.Separable.CutFactorization (descentAt)
private def descentSet {n : ℕ} (π : Equiv.Perm (Fin n)) : Finset ℕ :=
  (univ.filter (fun i => descentAt π i ≠ 0)).image (fun i => i.val + 1)
private theorem mem_descentSet {n : ℕ} (π : Equiv.Perm (Fin n)) (a : ℕ) :
    a ∈ descentSet π ↔ ∃ i : Fin n, descentAt π i ≠ 0 ∧ i.val + 1 = a := by
  simp [descentSet]
private theorem descentSet_subset_iff {n : ℕ} (π : Equiv.Perm (Fin n)) (U : Finset ℕ) :
    descentSet π ⊆ U ↔ ∀ i : Fin n, descentAt π i ≠ 0 → i.val + 1 ∈ U := by
  simp only [Finset.subset_iff, mem_descentSet]
  constructor
  · intro h i hi; exact h (by exact ⟨i, hi, rfl⟩)
  · intro h a ha; obtain ⟨i, hi, rfl⟩ := ha; exact h i hi
private theorem descentAt_zero_or_one {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    descentAt π i = 0 ∨ descentAt π i = 1 := by
  unfold descentAt
  split_ifs <;> simp
private theorem maj_eq_sum_descentSet {n : ℕ} (π : Equiv.Perm (Fin n)) :
    maj π = ∑ a ∈ descentSet π, a := by
  rw [descentSet, sum_image]
  · rw [sum_filter]
    apply sum_congr rfl
    intro i hi
    rcases descentAt_zero_or_one π i with h | h <;> simp [h]
  · intro a ha b hb he
    apply Fin.ext
    change a.val + 1 = b.val + 1 at he
    omega
private theorem mem_descentSets_iff (k : ℕ) (S : Finset ℕ) :
    S ∈ D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629.partitions k ↔ S ⊆ Icc 1 k ∧ (∑ a ∈ S, a) = k := by
  simp [D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629.partitions]
private theorem maj_eq_iff_descentSet_mem {n k : ℕ} (π : Equiv.Perm (Fin n)) :
    maj π = k ↔ descentSet π ∈ D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629.partitions k := by
  rw [mem_descentSets_iff, maj_eq_sum_descentSet]
  constructor
  · intro h
    refine ⟨?_, h⟩
    intro a ha
    apply mem_Icc.mpr
    have hpos : 1 ≤ a := by
      obtain ⟨i, hi, rfl⟩ := (mem_descentSet π a).mp ha
      omega
    refine ⟨hpos, ?_⟩
    rw [← h]
    exact single_le_sum (f := fun x : ℕ => x) (fun i hi => Nat.zero_le i) ha
  · exact And.right
private theorem sum_by_descentSet {n k : ℕ} (w : Equiv.Perm (Fin n) → ℚ) :
    (∑ π ∈ univ.filter (fun π => maj π = k), w π) =
      ∑ S ∈ D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629.partitions k, ∑ π ∈ univ.filter (fun π => descentSet π = S), w π := by
  have h := sum_fiberwise_eq_sum_filter
    (univ : Finset (Equiv.Perm (Fin n))) (D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629.partitions k) descentSet w
  rw [h]
  apply sum_congr
  · ext π
    simp [maj_eq_iff_descentSet_mem]
  · intro π hπ; rfl

end D5.S1.Words.Permutations.KageyMajorIndexFirstLetter

namespace D5.S1.Words.Permutations.KageyMajorIndexFirstLetter
open Finset Polynomial Blocks D5.S1.Words.Permutations.OrderedBlockAllocations
private theorem countPoly_eval_descent {n : ℕ} (U : Finset ℕ) (hm : (U.sup id) ≤ n) :
    (countPoly U).eval (n : ℚ) =
      ∑ π ∈ univ.filter (fun π : Equiv.Perm (Fin n) => descentSet π ⊆ U), (1 : ℚ) := by
  rw [countPoly_eval U hm]
  have hc : Fintype.card {π : Equiv.Perm (Fin n) // IncreasingOnBlocks (@cutLabel U n) π} =
      Fintype.card (Allocation (@cutLabel U n)) := by
    convert! card_increasingOnBlocks (@cutLabel U n) using 1 <;> congr!
  rw [← hc]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [Fintype.card_subtype]
  congr 1
  ext π
  simp only [mem_filter, mem_univ, true_and, descentSet_subset_iff,
    increasingOnBlocks_iff_descents]
private theorem weightedPoly_eval_descent {n : ℕ} (hn : 0 < n) (U : Finset ℕ)
    (hpos : ∀ u ∈ U, 0 < u) (hm : (U.sup id) ≤ n) :
    (weightedPoly U).eval (n : ℚ) =
      ∑ π ∈ univ.filter (fun π : Equiv.Perm (Fin n) => descentSet π ⊆ U),
        ((if h : 0 < n then (π ⟨0, h⟩).val + 1 else 0 : ℕ) : ℚ) := by
  rw [weightedPoly_eval hn U hpos hm]
  symm
  apply Finset.sum_subtype
  intro π
  simp only [mem_filter, mem_univ, true_and, descentSet_subset_iff,
    increasingOnBlocks_iff_descents]
private noncomputable def A (k : ℕ) : Polynomial ℚ :=
  ∑ S ∈ D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629.partitions k, ∑ U ∈ S.powerset,
    C ((-1 : ℚ) ^ (S.card - U.card)) * countPoly U
private noncomputable def B (k : ℕ) : Polynomial ℚ :=
  ∑ S ∈ D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629.partitions k, ∑ U ∈ S.powerset,
    C ((-1 : ℚ) ^ (S.card - U.card)) * weightedPoly U
private theorem cutMax_le_of_subsets {k : ℕ} {S U : Finset ℕ}
    (hS : S ∈ D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629.partitions k) (hU : U ⊆ S) : (U.sup id) ≤ k := by
  apply Finset.sup_le
  intro u hu
  exact (mem_Icc.mp (((mem_descentSets_iff k S).mp hS).1 (hU hu))).2
private theorem pos_of_subsets {k : ℕ} {S U : Finset ℕ}
    (hS : S ∈ D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629.partitions k) (hU : U ⊆ S) : ∀ u ∈ U, 0 < u := by
  intro u hu
  exact (mem_Icc.mp (((mem_descentSets_iff k S).mp hS).1 (hU hu))).1
private theorem A_eval {n k : ℕ} (hn : k ≤ n) : (A k).eval (n : ℚ) = count n k := by
  calc
    (A k).eval (n : ℚ) =
        ∑ S ∈ D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629.partitions k, ∑ π ∈ univ.filter (fun π : Equiv.Perm (Fin n) => descentSet π = S), (1 : ℚ) := by
      simp only [A, eval_finset_sum, eval_mul, eval_C]
      apply sum_congr rfl
      intro S hS
      rw [exact_descent_inclusion_exclusion descentSet S (fun _ => (1 : ℚ))]
      apply sum_congr rfl
      intro U hU
      rw [countPoly_eval_descent U ((cutMax_le_of_subsets hS (mem_powerset.mp hU)).trans hn)]
    _ = ∑ π ∈ univ.filter (fun π : Equiv.Perm (Fin n) => maj π = k), (1 : ℚ) :=
      (sum_by_descentSet _).symm
    _ = count n k := by simp [count]
private theorem B_eval {n k : ℕ} (hk : 0 < k) (hn : k ≤ n) : (B k).eval (n : ℚ) =
    ∑ π ∈ univ.filter (fun π : Equiv.Perm (Fin n) => maj π = k), ((if h : 0 < n then (π ⟨0, h⟩).val + 1 else 0 : ℕ) : ℚ) := by
  rw [sum_by_descentSet]
  simp only [B, eval_finset_sum, eval_mul, eval_C]
  apply sum_congr rfl
  intro S hS
  rw [exact_descent_inclusion_exclusion descentSet S (fun π => ((if h : 0 < n then (π ⟨0, h⟩).val + 1 else 0 : ℕ) : ℚ))]
  apply sum_congr rfl
  intro U hU
  rw [weightedPoly_eval_descent (hk.trans_le hn) U
    (pos_of_subsets hS (mem_powerset.mp hU))
    ((cutMax_le_of_subsets hS (mem_powerset.mp hU)).trans hn)]

end D5.S1.Words.Permutations.KageyMajorIndexFirstLetter

namespace D5.S1.Words.Permutations.KageyMajorIndexFirstLetter
open Finset Polynomial Blocks D5.S1.Words.Permutations.OrderedBlockAllocations
private theorem singleton_mem_descentSets {k : ℕ} (hk : 0 < k) : {k} ∈ D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629.partitions k := by
  simp [mem_descentSets_iff, Nat.succ_le_iff, hk]
private theorem cutMax_singleton (k : ℕ) : ({k} : Finset ℕ).sup id = k := by simp
private theorem top_pair_unique {k : ℕ} (hk : 0 < k) {S U : Finset ℕ}
    (hS : S ∈ D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629.partitions k) (hU : U ⊆ S) (hmax : (U.sup id) = k) :
    S = {k} ∧ U = {k} := by
  have hkU : k ∈ U := by
    by_contra hh
    have hlt : (U.sup id) < k := by
      apply (Finset.sup_lt_iff hk).mpr
      intro u hu
      have hu_le := (mem_Icc.mp (((mem_descentSets_iff k S).mp hS).1 (hU hu))).2
      exact lt_of_le_of_ne hu_le (fun he => hh (he ▸ hu))
    omega
  have hkS := hU hkU
  have hSeq : S = {k} := by
    apply eq_singleton_iff_unique_mem.mpr
    refine ⟨hkS, ?_⟩
    intro a ha
    by_contra hne
    have hsum := ((mem_descentSets_iff k S).mp hS).2
    have he := sum_erase_add S (fun x : ℕ => x) hkS
    have ha' : a ∈ S.erase k := mem_erase.mpr ⟨hne, ha⟩
    have hle := single_le_sum (fun x (_ : x ∈ S.erase k) => Nat.zero_le x) ha'
    have hpos := (mem_Icc.mp (((mem_descentSets_iff k S).mp hS).1 ha)).1
    omega
  refine ⟨hSeq, ?_⟩
  apply subset_antisymm
  · simpa [hSeq] using hU
  · exact singleton_subset_iff.mpr hkU
private theorem blockDenom_singleton (k : ℕ) : blockDenom {k} = k.factorial := by
  have hlabel (i : Fin k) : cutLabel {k} i = 0 := by
    apply Fin.ext
    simp [cutLabel, not_le_of_gt i.isLt]
  have hc : Fintype.card ({aFiber // (@cutLabel {k} k) aFiber = 0}) = k := by
    rw [Fintype.card_subtype]
    simp [hlabel]
  unfold blockDenom
  rw [cutMax_singleton]
  have he : (univ : Finset (Fin (({k} : Finset ℕ).card + 1))).erase ((Fin.last ({k} : Finset ℕ).card)) = {0} := by
    change (univ : Finset (Fin 2)).erase 1 = {0}
    rw [Finset.univ_fin2]
    decide
  rw [he, prod_singleton, hc]
private theorem weightedPoly_natDegree_le (U : Finset ℕ) :
    (weightedPoly U).natDegree ≤ (U.sup id) + 1 := by
  rcases U.eq_empty_or_nonempty with rfl | hU
  · simp
  · exact (weightedPoly_natDegree_nonempty U hU).le
private theorem weightedPoly_leadingCoeff_nonempty (U : Finset ℕ) (hU : U.Nonempty) :
    (weightedPoly U).leadingCoeff =
      (((U.min' hU + 1 : ℕ) : ℚ)⁻¹) * (blockDenom U : ℚ)⁻¹ := by
  have hX : (X + 1 : Polynomial ℚ).leadingCoeff = 1 := by
    simpa using (monic_X_add_C (1 : ℚ)).leadingCoeff
  rw [weightedPoly, dif_pos hU, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C,
    hX, mul_one, countPoly_leadingCoeff]
private theorem countPoly_singleton_top (k : ℕ) :
    (countPoly {k}).coeff k = (k.factorial : ℚ)⁻¹ := by
  have hd : (countPoly {k}).natDegree = k := by rw [countPoly_natDegree, cutMax_singleton]
  calc
    _ = (countPoly {k}).coeff (countPoly {k}).natDegree := by rw [hd]
    _ = _ := by rw [coeff_natDegree, countPoly_leadingCoeff, blockDenom_singleton]
private theorem weightedPoly_singleton_top (k : ℕ) :
    (weightedPoly {k}).coeff (k + 1) = ((k + 1).factorial : ℚ)⁻¹ := by
  have hn : ({k} : Finset ℕ).Nonempty := singleton_nonempty k
  have hd : (weightedPoly {k}).natDegree = k + 1 := by
    rw [weightedPoly_natDegree_nonempty {k} hn, cutMax_singleton]
  calc
    _ = (weightedPoly {k}).coeff (weightedPoly {k}).natDegree := by rw [hd]
    _ = _ := by
      rw [coeff_natDegree, weightedPoly_leadingCoeff_nonempty {k} hn, blockDenom_singleton]
      simp [Nat.factorial_succ, mul_inv_rev, mul_comm]
private theorem A_natDegree_le (k : ℕ) : (A k).natDegree ≤ k := by
  apply natDegree_sum_le_of_forall_le
  intro S hS
  apply natDegree_sum_le_of_forall_le
  intro U hU
  exact (natDegree_C_mul_le _ _).trans ((countPoly_natDegree U).le.trans
    (cutMax_le_of_subsets hS (mem_powerset.mp hU)))
private theorem B_natDegree_le (k : ℕ) : (B k).natDegree ≤ k + 1 := by
  apply natDegree_sum_le_of_forall_le
  intro S hS
  apply natDegree_sum_le_of_forall_le
  intro U hU
  exact (natDegree_C_mul_le _ _).trans ((weightedPoly_natDegree_le U).trans
    (Nat.add_le_add_right (cutMax_le_of_subsets hS (mem_powerset.mp hU)) 1))
private theorem countPoly_top_vanish {k : ℕ} (hk : 0 < k) {S U : Finset ℕ}
    (hS : S ∈ D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629.partitions k) (hU : U ⊆ S) (hne : S ≠ {k} ∨ U ≠ {k}) :
    (countPoly U).coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  rw [countPoly_natDegree]
  apply lt_of_le_of_ne (cutMax_le_of_subsets hS hU)
  intro he
  have hp := top_pair_unique hk hS hU he
  exact hne.elim (fun h => h hp.1) (fun h => h hp.2)
private theorem weightedPoly_top_vanish {k : ℕ} (hk : 0 < k) {S U : Finset ℕ}
    (hS : S ∈ D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629.partitions k) (hU : U ⊆ S) (hne : S ≠ {k} ∨ U ≠ {k}) :
    (weightedPoly U).coeff (k + 1) = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  apply (weightedPoly_natDegree_le U).trans_lt
  apply Nat.add_lt_add_right
  apply lt_of_le_of_ne (cutMax_le_of_subsets hS hU)
  intro he
  have hp := top_pair_unique hk hS hU he
  exact hne.elim (fun h => h hp.1) (fun h => h hp.2)
private theorem A_top {k : ℕ} (hk : 0 < k) : (A k).coeff k = (k.factorial : ℚ)⁻¹ := by
  simp only [A, finsetSum_coeff, coeff_C_mul]
  rw [sum_eq_single {k}]
  · rw [sum_eq_single {k}]
    · simp [countPoly_singleton_top]
    · intro U hU hne
      rw [countPoly_top_vanish hk (singleton_mem_descentSets hk) (mem_powerset.mp hU) (Or.inr hne), mul_zero]
    · simp
  · intro S hS hne
    apply sum_eq_zero
    intro U hU
    rw [countPoly_top_vanish hk hS (mem_powerset.mp hU) (Or.inl hne), mul_zero]
  · exact fun h => (h (singleton_mem_descentSets hk)).elim
private theorem B_top {k : ℕ} (hk : 0 < k) : (B k).coeff (k + 1) = ((k + 1).factorial : ℚ)⁻¹ := by
  simp only [B, finsetSum_coeff, coeff_C_mul]
  rw [sum_eq_single {k}]
  · rw [sum_eq_single {k}]
    · simp [weightedPoly_singleton_top]
    · intro U hU hne
      rw [weightedPoly_top_vanish hk (singleton_mem_descentSets hk) (mem_powerset.mp hU) (Or.inr hne), mul_zero]
    · simp
  · intro S hS hne
    apply sum_eq_zero
    intro U hU
    rw [weightedPoly_top_vanish hk hS (mem_powerset.mp hU) (Or.inl hne), mul_zero]
  · exact fun h => (h (singleton_mem_descentSets hk)).elim
private noncomputable def Q (k : ℕ) : Polynomial ℚ := C (k.factorial : ℚ) * A k
private noncomputable def P (k : ℕ) : Polynomial ℚ := C ((k + 1).factorial : ℚ) * B k
private theorem Q_monic_degree {k : ℕ} (hk : 0 < k) : (Q k).Monic ∧ (Q k).natDegree = k := by
  have hfac : (k.factorial : ℚ) ≠ 0 := by positivity
  have hcoeff : (Q k).coeff k = 1 := by rw [Q, coeff_C_mul, A_top hk, mul_inv_cancel₀ hfac]
  have hle : (Q k).natDegree ≤ k := (natDegree_C_mul_le _ _).trans (A_natDegree_le k)
  have hd := natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hcoeff]; exact one_ne_zero)
  refine ⟨?_, hd⟩
  change (Q k).coeff (Q k).natDegree = 1
  rw [hd, hcoeff]
private theorem P_monic_degree {k : ℕ} (hk : 0 < k) : (P k).Monic ∧ (P k).natDegree = k + 1 := by
  have hfac : ((k + 1).factorial : ℚ) ≠ 0 := by positivity
  have hcoeff : (P k).coeff (k + 1) = 1 := by rw [P, coeff_C_mul, B_top hk, mul_inv_cancel₀ hfac]
  have hle : (P k).natDegree ≤ k + 1 := (natDegree_C_mul_le _ _).trans (B_natDegree_le k)
  have hd := natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hcoeff]; exact one_ne_zero)
  refine ⟨?_, hd⟩
  change (P k).coeff (P k).natDegree = 1
  rw [hd, hcoeff]
theorem result : claim := by
  intro k hk
  obtain ⟨hP, hdP⟩ := P_monic_degree hk
  obtain ⟨hQ, hdQ⟩ := Q_monic_degree hk
  refine ⟨P k, Q k, hP, hQ, hdP, hdQ, ?_⟩
  intro n hn hne
  have hfac : (k.factorial : ℚ) ≠ 0 := by positivity
  have hkQ : (k + 1 : ℚ) ≠ 0 := Nat.cast_add_one_ne_zero k
  rw [E, P, Q, eval_mul, eval_C, eval_mul, eval_C, A_eval hn, B_eval hk hn]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

end D5.S1.Words.Permutations.KageyMajorIndexFirstLetter

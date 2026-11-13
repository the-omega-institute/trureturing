/- GID: D5/S3/Combinatorics/PermutationArrays/EtiennePrefixCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PermutationArrays/EtiennePrefixCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Order.Interval.Finset.Fin, mathlib/module/Mathlib.SetTheory.Cardinal.Finite]
   utility: none
   digest: Literal sorted width-two binary matrices with bounded rectangle prefixes. -/

import Mathlib.Order.Interval.Finset.Fin
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! # Literal width-two prefix matrices and their four consecutive row blocks -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PermutationArrays.EtiennePrefixCount

open Finset

/-- Actual labeled binary matrices; there is no quotient by row or column permutations. -/
abbrev Matrix (n : ℕ) := Fin n → Fin 2 → Bool

/-- The increasing lexicographic row ranks are exactly 00,01,10,11. -/
def rank (r : Fin 2 → Bool) : ℕ := 2 * (r 0).toNat + (r 1).toNat

/-- Column words are compared at their first unequal entry, with false before true. -/
def ColumnsLE {n : ℕ} (M : Matrix n) : Prop :=
  (∀ i, M i 0 = M i 1) ∨
    ∃ i, M i 0 = false ∧ M i 1 = true ∧ ∀ k, k < i → M k 0 = M k 1

/-- Zero extension is used only to write finite rectangle sums with natural endpoints. -/
def cell {n : ℕ} (M : Matrix n) (r c : ℕ) : ℕ :=
  if hr : r < n then if hc : c < 2 then (M ⟨r, hr⟩ ⟨c, hc⟩).toNat else 0 else 0

/-- Number of ones in the literal top-left i by j rectangle. -/
def ones {n : ℕ} (M : Matrix n) (i j : ℕ) : ℕ :=
  ∑ r ∈ range i, ∑ c ∈ range j, cell M r c

/-- Every nonempty in-bounds rectangle prefix has at most half ones. -/
def PrefixBound {n : ℕ} (M : Matrix n) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n → ∀ j, 1 ≤ j → j ≤ 2 → 2 * ones M i j ≤ i * j

/-- Both lexicographic constraints and all rectangle-prefix constraints on actual matrices. -/
abbrev Arrays (n : ℕ) :=
  {M : Matrix n // Monotone (fun i => rank (M i)) ∧ ColumnsLE M ∧ PrefixBound M}

/-- The sequence is defined by its literal matrix subtype, independently of any formula. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card (Arrays n)

/-- The complete integer form of Etienne's conjecture, for every original positive height. -/
def claim : Prop := ∀ n : ℕ, 1 ≤ n →
  32 * (a n : ℤ) = 2 * (n : ℤ) ^ 3 + 11 * (n : ℤ) ^ 2 + 31 * n + 27 +
    ((n : ℤ) ^ 2 + n + 5) * (-1 : ℤ) ^ n

/-- Three cuts describe the four consecutive row blocks, including empty blocks. -/
structure Cuts (n : ℕ) where
  p : ℕ
  q : ℕ
  r : ℕ
  pq : p ≤ q
  qr : q ≤ r
  rn : r ≤ n

/-- Rows are 00 before p, 01 up to q, 10 up to r, and 11 thereafter. -/
def blockMatrix {n : ℕ} (u : Cuts n) : Matrix n := fun i j =>
  if j = 0 then decide (u.q ≤ i.val)
  else decide ((u.p ≤ i.val ∧ i.val < u.q) ∨ u.r ≤ i.val)

/-- A monotone word's strict sublevel set is its initial segment of the corresponding size. -/
private theorem lt_sublevel_card {n : ℕ} (f : Fin n → ℕ) (hf : Monotone f)
    (i : Fin n) (k : ℕ) :
    f i < k ↔ i.val < (univ.filter (fun j => f j < k)).card := by
  constructor
  · intro hi
    have hsub : Iic i ⊆ univ.filter (fun j => f j < k) := by
      intro j hj
      exact mem_filter.mpr ⟨mem_univ _, lt_of_le_of_lt (hf (mem_Iic.mp hj)) hi⟩
    have hcard := card_le_card hsub
    simp only [Fin.card_Iic] at hcard
    omega
  · intro hi
    by_contra h
    have hsub : univ.filter (fun j => f j < k) ⊆ Iio i := by
      intro j hj
      have hjk := (mem_filter.mp hj).2
      have : ¬ i ≤ j := fun hij => h (lt_of_le_of_lt (hf hij) hjk)
      exact mem_Iio.mpr (lt_of_not_ge this)
    have hcard := card_le_card hsub
    simp only [Fin.card_Iio] at hcard
    omega

/-- Extract the three actual row-rank sublevel sizes. -/
private def extractCuts {n : ℕ} (M : Matrix n) : Cuts n where
  p := (univ.filter (fun i => rank (M i) < 1)).card
  q := (univ.filter (fun i => rank (M i) < 2)).card
  r := (univ.filter (fun i => rank (M i) < 3)).card
  pq := card_le_card (by intro i hi; simp only [mem_filter, mem_univ, true_and] at hi ⊢; omega)
  qr := card_le_card (by intro i hi; simp only [mem_filter, mem_univ, true_and] at hi ⊢; omega)
  rn := by simpa using card_le_card (filter_subset (fun i => rank (M i) < 3) univ)

/-- Extraction reconstructs every sorted literal matrix, without changing its labels. -/
private theorem block_extract {n : ℕ} (M : Matrix n)
    (hM : Monotone (fun i => rank (M i))) : blockMatrix (extractCuts M) = M := by
  funext i j
  have h1 := lt_sublevel_card (fun i => rank (M i)) hM i 1
  have h2 := lt_sublevel_card (fun i => rank (M i)) hM i 2
  have h3 := lt_sublevel_card (fun i => rank (M i)) hM i 3
  change rank (M i) < 1 ↔ i.val < (extractCuts M).p at h1
  change rank (M i) < 2 ↔ i.val < (extractCuts M).q at h2
  change rank (M i) < 3 ↔ i.val < (extractCuts M).r at h3
  fin_cases j <;> cases h0 : M i 0 <;> cases h4 : M i 1 <;>
    simp only [rank, h0, h4, Bool.toNat_false, Bool.toNat_true] at h1 h2 h3 <;>
    simp_all [blockMatrix] <;> omega

/-- Every four-block matrix has the required weak row order. -/
private theorem block_sorted {n : ℕ} (u : Cuts n) :
    Monotone (fun i => rank (blockMatrix u i)) := by
  intro i j hij
  have hij' : i.val ≤ j.val := hij
  have hpq := u.pq
  have hqr := u.qr
  by_cases hpi : u.p ≤ i.val <;> by_cases hqi : u.q ≤ i.val <;>
    by_cases hri : u.r ≤ i.val <;> by_cases hpj : u.p ≤ j.val <;>
    by_cases hqj : u.q ≤ j.val <;> by_cases hrj : u.r ≤ j.val <;>
    simp [rank, blockMatrix, hpi, hqi, hri, hpj, hqj, hrj,
      show (i.val < u.q) ↔ ¬ u.q ≤ i.val from Nat.lt_iff_not_ge,
      show (j.val < u.q) ↔ ¬ u.q ≤ j.val from Nat.lt_iff_not_ge] <;> omega

/-- The first unequal columns have row 01 exactly when its block is nonempty. -/
private theorem columns_block_iff {n : ℕ} (u : Cuts n) :
    ColumnsLE (blockMatrix u) ↔ u.p < u.q ∨ u.q = u.r := by
  have hpq := u.pq
  have hqr := u.qr
  have hrn := u.rn
  constructor
  · rintro (heq | ⟨i, hl, hr, _⟩)
    · right
      by_contra h
      have hlt : u.q < u.r := by omega
      have hqn : u.q < n := by omega
      have hh := heq ⟨u.q, hqn⟩
      simp [blockMatrix, show ¬ u.r ≤ u.q by omega] at hh
    · left
      simp [blockMatrix] at hl hr
      omega
  · intro h
    by_cases hp : u.p < u.q
    · refine Or.inr ⟨⟨u.p, by omega⟩, ?_, ?_, ?_⟩
      · simp [blockMatrix, show ¬ u.q ≤ u.p by omega]
      · simp [blockMatrix, hp]
      · intro k hk
        have hk' : k.val < u.p := hk
        simp [blockMatrix, show ¬ u.q ≤ k.val by omega,
          show ¬ u.p ≤ k.val by omega, show ¬ u.r ≤ k.val by omega]
    · have hp' : u.p = u.q := by omega
      have hr' : u.r = u.q := by omega
      left
      intro i
      by_cases hi : u.q ≤ i.val <;> simp [blockMatrix, hp', hr', hi] <;> omega

/-- Both literal rectangle sums have explicit formulas at every prefix height. -/
private theorem ones_block {n : ℕ} (u : Cuts n) (i : ℕ) (hi : i ≤ n) :
    ones (blockMatrix u) i 1 = i - u.q ∧
    ones (blockMatrix u) i 2 = (i - u.p) + (i - u.r) := by
  induction i with
  | zero => simp [ones]
  | succ i ih =>
    have hin : i < n := by omega
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hs1 : ones (blockMatrix u) (i + 1) 1 =
        ones (blockMatrix u) i 1 + cell (blockMatrix u) i 0 := by
      simp [ones, sum_range_succ]
    have hs2 : ones (blockMatrix u) (i + 1) 2 =
        ones (blockMatrix u) i 2 +
          (cell (blockMatrix u) i 0 + cell (blockMatrix u) i 1) := by
      simp [ones, sum_range_succ, add_assoc]
    have hc1 : cell (blockMatrix u) i 0 = if u.q ≤ i then 1 else 0 := by
      by_cases hq : u.q ≤ i <;> simp [cell, blockMatrix, hin, hq]
    have hc2 : cell (blockMatrix u) i 0 + cell (blockMatrix u) i 1 =
        (if u.p ≤ i then 1 else 0) + (if u.r ≤ i then 1 else 0) := by
      have hpq := u.pq
      have hqr := u.qr
      by_cases hp : u.p ≤ i <;> by_cases hq : u.q ≤ i <;>
        by_cases hr : u.r ≤ i <;> simp [cell, blockMatrix, hin, hp, hq, hr] <;> omega
    rw [hs1, hs2, ih1, ih2, hc2, hc1]
    constructor <;> split_ifs <;> omega

/-- All prefix constraints are equivalent to the two full-height endpoint inequalities. -/
private theorem prefix_block_iff {n : ℕ} (u : Cuts n) :
    PrefixBound (blockMatrix u) ↔ n - u.q ≤ u.q ∧ n - u.r ≤ u.p := by
  have hpq := u.pq
  have hqr := u.qr
  have hrn := u.rn
  constructor
  · intro h
    by_cases hn : 1 ≤ n
    · have h1 := h n hn le_rfl 1 (by omega) (by omega)
      have h2 := h n hn le_rfl 2 (by omega) (by omega)
      rw [(ones_block u n le_rfl).1] at h1
      rw [(ones_block u n le_rfl).2] at h2
      omega
    · omega
  · rintro ⟨h1, h2⟩ i _ hi j hj hj2
    have hh := ones_block u i hi
    interval_cases j
    · rw [hh.1]
      omega
    · rw [hh.2]
      omega

/-- The three cuts are read directly from row ranks, even when some blocks are empty. -/
private theorem block_rank_lt {n : ℕ} (u : Cuts n) (i : Fin n) :
    (rank (blockMatrix u i) < 1 ↔ i.val < u.p) ∧
    (rank (blockMatrix u i) < 2 ↔ i.val < u.q) ∧
    (rank (blockMatrix u i) < 3 ↔ i.val < u.r) := by
  have hpq := u.pq
  have hqr := u.qr
  by_cases hp : u.p ≤ i.val <;> by_cases hq : u.q ≤ i.val <;>
    by_cases hr : u.r ≤ i.val <;>
    simp [rank, blockMatrix, hp, hq, hr, ← Nat.not_le] <;> omega

/-- Distinct cut triples give distinct actual labeled matrices. -/
private theorem block_injective (n : ℕ) :
    Function.Injective (@blockMatrix n) := by
  intro u v huv
  have cut_ext (a b : ℕ) (ha : a ≤ n) (hb : b ≤ n)
      (h : ∀ i : Fin n, i.val < a ↔ i.val < b) : a = b := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hba
    · have hh := h ⟨a, by omega⟩
      simp only [lt_self_iff_false, false_iff] at hh
      omega
    · have hh := h ⟨b, by omega⟩
      simp only [lt_self_iff_false, iff_false] at hh
      omega
  have hp : u.p = v.p := cut_ext u.p v.p (by have := u.pq; have := u.qr; have := u.rn; omega)
      (by have := v.pq; have := v.qr; have := v.rn; omega) (fun i => by
        rw [← (block_rank_lt u i).1, ← (block_rank_lt v i).1, huv])
  have hq : u.q = v.q := cut_ext u.q v.q (by have := u.qr; have := u.rn; omega)
      (by have := v.qr; have := v.rn; omega) (fun i => by
        rw [← (block_rank_lt u i).2.1, ← (block_rank_lt v i).2.1, huv])
  have hr : u.r = v.r := cut_ext u.r v.r u.rn v.rn (fun i => by
    rw [← (block_rank_lt u i).2.2, ← (block_rank_lt v i).2.2, huv])
  cases u
  cases v
  simp_all

/-- Cuts satisfying precisely the column-order and two prefix endpoint conditions. -/
private abbrev ValidCuts (n : ℕ) :=
  {u : Cuts n // (u.p < u.q ∨ u.q = u.r) ∧ n - u.q ≤ u.q ∧ n - u.r ≤ u.p}

private def assemble (n : ℕ) (u : ValidCuts n) : Arrays n :=
  ⟨blockMatrix u.1, block_sorted u.1,
    (columns_block_iff u.1).mpr u.2.1, (prefix_block_iff u.1).mpr u.2.2⟩

/-- This bijection reconstructs the literal matrix in one direction and its unique cuts in the other. -/
private theorem assemble_bijective (n : ℕ) : Function.Bijective (assemble n) := by
  constructor
  · intro u v h
    apply Subtype.ext
    exact block_injective n (congrArg Subtype.val h)
  · intro M
    let u := extractCuts M.1
    have hu : blockMatrix u = M.1 := block_extract M.1 M.2.1
    have hc : ColumnsLE (blockMatrix u) := hu.symm ▸ M.2.2.1
    have hp : PrefixBound (blockMatrix u) := hu.symm ▸ M.2.2.2
    refine ⟨⟨u, (columns_block_iff u).mp hc, (prefix_block_iff u).mp hp⟩, ?_⟩
    exact Subtype.ext hu

private noncomputable def arrayEquiv (n : ℕ) : Arrays n ≃ ValidCuts n :=
  (Equiv.ofBijective (assemble n) (assemble_bijective n)).symm

end D5.S3.Combinatorics.PermutationArrays.EtiennePrefixCount

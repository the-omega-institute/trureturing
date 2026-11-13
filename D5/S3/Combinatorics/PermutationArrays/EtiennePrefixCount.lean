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
  fin_cases j <;> cases h0 : M i 0 <;> cases h4 : M i 1 <;>
    simp only [rank, h0, h4, Bool.toNat_false, Bool.toNat_true] at h1 h2 h3 <;>
    simp [blockMatrix, extractCuts, h1, h2, h3] <;> omega

end D5.S3.Combinatorics.PermutationArrays.EtiennePrefixCount

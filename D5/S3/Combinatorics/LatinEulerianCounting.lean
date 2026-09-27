/- GID: D5/S3/Combinatorics/LatinEulerianCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LatinEulerianCounting
   mirror-E: none(waiver:direct-finite-incidence-count-for-Latin-ascents)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Basic]
   utility: none
   digest: Counting ascent incidences by rows gives the fixed column-ascent total. -/

import D5.S3.Combinatorics.LatinEulerianDefs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.Rev

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LatinEulerianMultiples

/-- Number of ascending columns across rows `j` and `j+1`. -/
def rowAscents (n : ℕ) (L : Fin n → Fin n → Fin n) (j : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter
    (fun c => ∃ (h : j + 1 < n), L ⟨j, by omega⟩ c < L ⟨j + 1, h⟩ c)).card

/-- Reverse the order of the rows without changing any symbol or column. -/
def reverseRows (n : ℕ) (L : Fin n → Fin n → Fin n) : Fin n → Fin n → Fin n :=
  fun i c => L i.rev c

theorem rowAscents_reverse_add {n : ℕ} (hn : 2 ≤ n)
    (L : Fin n → Fin n → Fin n) (hL : IsLatin n L)
    {j : ℕ} (hj : j < n - 1) :
    rowAscents n (reverseRows n L) j + rowAscents n L (n - 2 - j) = n := by
  classical
  have hj' : j + 1 < n := by omega
  have hjlow : n - 2 - j + 1 < n := by omega
  have hrevlo : (⟨j + 1, hj'⟩ : Fin n).rev = ⟨n - 2 - j, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  have hrevhi : (⟨j, by omega⟩ : Fin n).rev = ⟨n - 2 - j + 1, hjlow⟩ := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  have hfilter : rowAscents n (reverseRows n L) j =
      ((Finset.univ : Finset (Fin n)).filter
        (fun c => ¬ L ⟨n - 2 - j, by omega⟩ c <
          L ⟨n - 2 - j + 1, hjlow⟩ c)).card := by
    unfold rowAscents reverseRows
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, hc⟩
      rw [hrevlo, hrevhi] at hc
      exact Fin.not_lt.mpr (le_of_lt hc)
    · intro hc
      have hidx : (⟨n - 2 - j, by omega⟩ : Fin n) ≠
          ⟨n - 2 - j + 1, hjlow⟩ := by
        intro heq
        have hv : n - 2 - j = n - 2 - j + 1 := congrArg Fin.val heq
        omega
      have hne : L ⟨n - 2 - j, by omega⟩ c ≠
          L ⟨n - 2 - j + 1, hjlow⟩ c := by
        exact fun heq => hidx ((hL.2 c).1 heq)
      refine ⟨hj', ?_⟩
      rw [hrevlo, hrevhi]
      exact lt_of_le_of_ne (le_of_not_gt hc) hne.symm
  have hplain : rowAscents n L (n - 2 - j) =
      ((Finset.univ : Finset (Fin n)).filter
        (fun c => L ⟨n - 2 - j, by omega⟩ c <
          L ⟨n - 2 - j + 1, hjlow⟩ c)).card := by
    simp [rowAscents, hjlow]
  rw [hfilter, hplain, add_comm]
  simpa using Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n)))
    (fun c => L ⟨n - 2 - j, by omega⟩ c < L ⟨n - 2 - j + 1, hjlow⟩ c)

theorem total_reverse {n : ℕ} (hn : 2 ≤ n)
    (L : Fin n → Fin n → Fin n) (hL : IsLatin n L) :
    totalAscents n (reverseRows n L) + totalAscents n L = n * (n - 1) := by
  have hrows (M : Fin n → Fin n → Fin n) :
      totalAscents n M = ∑ j ∈ Finset.range n, rowAscents n M j := by
    classical
    simp only [totalAscents, colAscents, rowAscents, Finset.card_eq_sum_ones,
      Finset.sum_filter]
    rw [Finset.sum_comm]
  have hlast : ∀ M : Fin n → Fin n → Fin n, rowAscents n M (n - 1) = 0 := by
    intro M
    have h : ¬ (n - 1 + 1 < n) := by omega
    simp [rowAscents, h]
  have hsum : ∀ M : Fin n → Fin n → Fin n,
      totalAscents n M = ∑ j ∈ Finset.range (n - 1), rowAscents n M j := by
    intro M
    rw [hrows]
    conv_lhs => arg 1; rw [show n = (n - 1) + 1 by omega]
    rw [Finset.sum_range_succ, hlast, add_zero]
  rw [hsum, hsum]
  calc
    (∑ j ∈ Finset.range (n - 1), rowAscents n (reverseRows n L) j) +
        ∑ j ∈ Finset.range (n - 1), rowAscents n L j =
      ∑ j ∈ Finset.range (n - 1),
        (rowAscents n (reverseRows n L) j + rowAscents n L (n - 2 - j)) := by
        rw [Finset.sum_add_distrib]
        congr 1
        calc
          (∑ j ∈ Finset.range (n - 1), rowAscents n L j) =
            ∑ j ∈ Finset.range (n - 1), rowAscents n L ((n - 1) - 1 - j) := by
              exact (Finset.sum_range_reflect (rowAscents n L) (n - 1)).symm
          _ = ∑ j ∈ Finset.range (n - 1), rowAscents n L (n - 2 - j) := by
            apply Finset.sum_congr rfl
            intro j hj
            congr 1
    _ = n * (n - 1) := by
      calc
        (∑ j ∈ Finset.range (n - 1),
            (rowAscents n (reverseRows n L) j + rowAscents n L (n - 2 - j))) =
          ∑ _j ∈ Finset.range (n - 1), n := by
            apply Finset.sum_congr rfl
            intro j hj
            exact rowAscents_reverse_add hn L hL (Finset.mem_range.mp hj)
        _ = n * (n - 1) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ac_rfl

end D5.S3.Combinatorics.LatinEulerianMultiples

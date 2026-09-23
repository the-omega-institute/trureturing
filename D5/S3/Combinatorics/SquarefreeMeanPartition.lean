/- GID: D5/S3/Combinatorics/SquarefreeMeanPartition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SquarefreeMeanPartition
   mirror-E: none(waiver:elementary-counting-argument)
   anchors: [mathlib/module/Mathlib.Algebra.Squarefree.Basic]
   utility: none
   digest: No squarefree number above one has a partition with equal means. -/

import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Combinatorics.SquarefreeMeanPartition

/-- No squarefree number above one admits a positive partition whose two means agree. -/
def claim : Prop :=
  ∀ n : ℕ, 1 < n → Squarefree n → ∀ D : Finset ℕ, ∀ m : ℕ → ℕ,
    (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 < m d) →
    (∑ d ∈ D, d * m d) = n → n * D.card = (∑ d ∈ D, m d) ^ 2 → False

/-- Equal means force all parts to be one, contradicting the number of distinct parts. -/
theorem result : claim := by
  intro n hn hsq D m hd hm htotal hmean
  let M := ∑ d ∈ D, m d
  let k := D.card
  have hn0 : n ≠ 0 := by omega
  have hmean' : n * k = M ^ 2 := by simpa [M, k] using hmean
  have hnM2 : n ∣ M ^ 2 := ⟨k, hmean'.symm⟩
  have hDne : D.Nonempty := by
    rcases D.eq_empty_or_nonempty with rfl | h
    · simp at htotal
      omega
    · exact h
  have hM0 : M ≠ 0 := by
    obtain ⟨d, hdD⟩ := hDne
    have hle : m d ≤ M := Finset.single_le_sum (fun i _ => Nat.zero_le (m i)) hdD
    have hpos := hm d hdD
    omega
  have hnM : n ∣ M := by
    rw [← Nat.factorization_le_iff_dvd hn0 hM0]
    have h2 : n.factorization ≤ (M ^ 2).factorization :=
      (Nat.factorization_le_iff_dvd hn0 (pow_ne_zero 2 hM0)).mpr hnM2
    rw [Nat.factorization_pow] at h2
    intro q
    have hq2 := h2 q
    simp only [Finsupp.smul_apply, smul_eq_mul] at hq2
    have hq1 := (Nat.squarefree_iff_factorization_le_one hn0).mp hsq q
    omega
  obtain ⟨j, hM⟩ := hnM
  -- Cancelling the positive squarefree number identifies the distinct-part count.
  have hk : k = n * j ^ 2 := by
    apply mul_left_cancel₀ hn0
    calc
      n * k = M ^ 2 := hmean'
      _ = (n * j) ^ 2 := by rw [hM]
      _ = n * (n * j ^ 2) := by ring
  have hkM : k ≤ M := by
    dsimp [k, M]
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun d hdD ↦ hm d hdD
  rw [hk, hM] at hkM
  have hj2j : j ^ 2 ≤ j := Nat.le_of_mul_le_mul_left hkM (by omega)
  have hD : D.Nonempty := by
    rcases D.eq_empty_or_nonempty with hD | hD
    · subst D
      simp at htotal
      omega
    · exact hD
  have hkpos : 0 < k := by simpa [k] using hD.card_pos
  have hjpos : 0 < j := by
    by_contra hj
    have : j = 0 := Nat.eq_zero_of_not_pos hj
    subst j
    simp at hk
    omega
  have hjle : j ≤ 1 := by
    have hmul : j * j ≤ j * 1 := by simpa [pow_two] using hj2j
    exact Nat.le_of_mul_le_mul_left hmul hjpos
  have hj : j = 1 := by omega
  have hcard : D.card = n := by simpa [k, hj] using hk
  -- A part above one makes the weighted total strictly exceed the number of parts.
  have hall : ∀ d ∈ D, d = 1 := by
    intro d hdD
    by_contra hd1
    have hdgt : 1 < d := by have := hd d hdD; omega
    have hsumlt : D.card < ∑ x ∈ D, x * m x := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_lt_sum
        (fun x hx ↦ mul_pos (hd x hx) (hm x hx))
        ⟨d, hdD, hdgt.trans_le (by
          simpa using Nat.mul_le_mul_left d (hm d hdD))⟩
    omega
  have hsubset : D ⊆ {1} := fun d hdD ↦ by simp [hall d hdD]
  have hcardle : D.card ≤ 1 := by
    simpa using Finset.card_le_card hsubset
  omega

end D5.S3.Combinatorics.SquarefreeMeanPartition

/- GID: D5/S3/Arith/Additive/ChuSquareCovering
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/ChuSquareCovering
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Group.Pointwise.Finset.Basic]
   utility: none
   digest: Sets A, B of sizes a, b in {0, ..., N-1} with A + B covering {0, ..., N-1} exist exactly when N <= ab, a <= N and b <= N; for N = n^2 the least common size is n. -/

import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-! M. Chu's question on additive covers of `{0, …, n² - 1}` (OEIS A000290), solved by
Proposition 9.1 of R. Blanco Gómez, Open statements in core entries of the OEIS, III (2026): the
least `k` such that some `A, B ⊆ {0, …, n² - 1}` with `|A| = |B| = k` satisfy
`A + B ⊇ {0, …, n² - 1}` is `n`.

`achievable_iff` determines every pair of sizes: sets `A, B ⊆ {0, …, N - 1}` with `|A| = a`,
`|B| = b` and `A + B ⊇ {0, …, N - 1}` exist exactly when `N ≤ ab`, `a ≤ N` and `b ≤ N`. The bound
`|A + B| ≤ |A| |B|` gives necessity; for sufficiency `{0, …, a - 1}` plus the multiples of `a`
below `N`, completed to `b` elements, covers `{0, …, N - 1}` by division by `a`.

admission_basis: escape-witness. Escape witnesses: cover (division by `a` covers the interval)
and card_multiples (at most `b` multiples of `a` lie below `N ≤ ab`). -/

set_option autoImplicit false

namespace D5.S3.Arith.Additive.ChuSquareCovering

open Finset
open scoped Pointwise

/-- `{0, …, N - 1}` is covered by `range a + (multiples of a below N)` when `a ≥ 1`. -/
private theorem cover (N a : ℕ) (ha : 0 < a) :
    range N ⊆ range a + (range N).filter (a ∣ ·) := by
  intro m hm
  rw [Finset.mem_add]
  refine ⟨m % a, Finset.mem_range.mpr (Nat.mod_lt _ ha), a * (m / a), ?_, Nat.mod_add_div m a⟩
  simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
  exact ⟨lt_of_le_of_lt (Nat.mul_div_le m a) hm, dvd_mul_right _ _⟩

/-- At most `b` multiples of `a` lie below `N` when `N ≤ a b`. -/
private theorem card_multiples (N a b : ℕ) (hN : N ≤ a * b) :
    ((range N).filter (a ∣ ·)).card ≤ b := by
  calc _ ≤ ((range b).image fun j => a * j).card := by
        apply Finset.card_le_card
        intro m hm
        simp only [Finset.mem_filter, Finset.mem_range] at hm
        obtain ⟨hmN, j, rfl⟩ := hm
        refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr ?_, rfl⟩
        by_contra hj
        push Not at hj
        have := Nat.mul_le_mul_left a hj
        omega
    _ ≤ (range b).card := Finset.card_image_le
    _ = b := Finset.card_range b

/-- Sizes `(a, b)` of sets `A, B ⊆ {0, …, N - 1}` with `A + B ⊇ {0, …, N - 1}`: exactly
`N ≤ a b`, `a ≤ N` and `b ≤ N`. -/
theorem achievable_iff (N a b : ℕ) :
    (∃ A B : Finset ℕ, A ⊆ range N ∧ B ⊆ range N ∧ A.card = a ∧ B.card = b ∧
      range N ⊆ A + B) ↔ N ≤ a * b ∧ a ≤ N ∧ b ≤ N := by
  constructor
  · rintro ⟨A, B, hA, hB, rfl, rfl, hcov⟩
    refine ⟨?_, ?_, ?_⟩
    · calc N = (range N).card := (card_range N).symm
        _ ≤ (A + B).card := card_le_card hcov
        _ ≤ A.card * B.card := card_add_le
    · simpa using card_le_card hA
    · simpa using card_le_card hB
  · rintro ⟨hN, haN, hbN⟩
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · refine ⟨∅, ∅, empty_subset _, empty_subset _, rfl, ?_, ?_⟩
      · have : N = 0 := by simpa using hN
        subst this; simp at hbN; simp [hbN]
      · have : N = 0 := by simpa using hN
        subst this; simp
    obtain ⟨B, hMB, hBN, hBcard⟩ := Finset.exists_subsuperset_card_eq
      (Finset.filter_subset (a ∣ ·) (range N))
      (card_multiples N a b hN) (by simpa using hbN)
    refine ⟨range a, B, ?_, hBN, card_range a, hBcard, ?_⟩
    · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    · exact (cover N a ha).trans (Finset.add_subset_add_left hMB)

/-- M. Chu's question, solved by Blanco Gómez: the least `k` for which some `A, B` of size `k`
in `{0, …, n² - 1}` have `A + B ⊇ {0, …, n² - 1}` is `n`. -/
theorem result (n : ℕ) :
    IsLeast {k | ∃ A B : Finset ℕ, A ⊆ range (n ^ 2) ∧ B ⊆ range (n ^ 2) ∧ A.card = k ∧
      B.card = k ∧ range (n ^ 2) ⊆ A + B} n := by
  refine ⟨(achievable_iff (n ^ 2) n n).mpr ⟨by rw [sq], ?_, ?_⟩, fun k hk => ?_⟩
  · rw [sq]; exact Nat.le_mul_self n
  · rw [sq]; exact Nat.le_mul_self n
  · have := ((achievable_iff (n ^ 2) k k).mp hk).1
    rw [sq] at this
    exact Nat.mul_self_le_mul_self_iff.mp this

end D5.S3.Arith.Additive.ChuSquareCovering

/- GID: D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums
   generality: I
   mirror-B: D5/B/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Moving-diagonal row differences prove Schulte's alternating Fibonacci harmonic sum. -/

import D5.S1.Recurrence.FibVajda

namespace D5.S1.Recurrence.Parity.HarmonicTriangleAlternatingRowSums

/-- Denominator of the Fibonacci harmonic triangle, OEIS A378277. -/
def denominator (n k : ℕ) : ℕ :=
  if k = n then Nat.fib n * Nat.fib (n + 1) else Nat.fib k * Nat.fib (k + 2)

/-- Alternating sum of the reciprocals in row `n`, starting with a positive term. -/
def altRowSum (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ (k - 1) / denominator n k

private theorem row_split (n : ℕ) :
    altRowSum (n + 1) =
      (∑ k ∈ Finset.Icc 1 n,
        (-1 : ℚ) ^ (k - 1) / ((Nat.fib k : ℚ) * Nat.fib (k + 2))) +
      (-1 : ℚ) ^ n / ((Nat.fib (n + 1) : ℚ) * Nat.fib (n + 2)) := by
  unfold altRowSum
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≠ n + 1 := by have := (Finset.mem_Icc.mp hk).2; omega
    simp [denominator, hkn]
  · simp [denominator, Nat.add_assoc]

/-- Moving the diagonal changes two terms; the unchanged row prefix cancels. -/
theorem altRowSum_succ_sub (n : ℕ) (hn : 2 ≤ n) :
    altRowSum (n + 1) - altRowSum n =
      2 * (-1 : ℚ) ^ n / ((Nat.fib (n + 1) : ℚ) * Nat.fib (n + 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [row_split (m + 1), row_split m,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
  simp only [Nat.add_sub_cancel, Nat.add_assoc, Nat.reduceAdd]
  have h1 : (Nat.fib (m + 1) : ℚ) ≠ 0 := by simp
  have h2 : (Nat.fib (m + 2) : ℚ) ≠ 0 := by simp
  have h3 : (Nat.fib (m + 3) : ℚ) ≠ 0 := by simp
  have hf : (Nat.fib (m + 3) : ℚ) = Nat.fib (m + 1) + Nat.fib (m + 2) := by
    exact_mod_cast (Nat.fib_add_two (n := m + 1))
  rw [pow_succ]
  field_simp
  rw [hf]
  ring

/-- The specialization of the repository's Vajda identity needed for the quotient step. -/
theorem fib_cassini_two (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) * Nat.fib (n + 3) -
      (Nat.fib n : ℤ) * Nat.fib (n + 4) = 2 * (-1 : ℤ) ^ (n + 2) := by
  have h := D5.S1.Recurrence.FibVajda.fib_vajda n 1 3
  norm_num [Nat.add_assoc, Nat.fib_add_two, pow_add] at h ⊢
  nlinarith [h]

private theorem quotient_step (m : ℕ) :
    (Nat.fib (m + 1) : ℚ) / Nat.fib (m + 4) -
      (Nat.fib m : ℚ) / Nat.fib (m + 3) =
      2 * (-1 : ℚ) ^ (m + 2) /
        ((Nat.fib (m + 3) : ℚ) * Nat.fib (m + 4)) := by
  have h : (Nat.fib (m + 1) : ℚ) * Nat.fib (m + 3) -
      (Nat.fib m : ℚ) * Nat.fib (m + 4) = 2 * (-1 : ℚ) ^ (m + 2) := by
    exact_mod_cast fib_cassini_two m
  have h3 : (Nat.fib (m + 3) : ℚ) ≠ 0 := by simp
  have h4 : (Nat.fib (m + 4) : ℚ) ≠ 0 := by simp
  field_simp
  linear_combination h

/-- Schulte's OEIS A378277 conjecture for every row from the second onward. -/
theorem schulte_conjecture (n : ℕ) (hn : 2 ≤ n) :
    altRowSum n = (Nat.fib (n - 2) : ℚ) / Nat.fib (n + 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [altRowSum, denominator, Finset.sum_Icc_succ_top, Nat.fib_add_two]
  | succ n hn ih =>
    have hr := altRowSum_succ_sub n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hq := quotient_step m
    simp only [Nat.add_sub_cancel, Nat.add_assoc, Nat.reduceAdd] at ih hr ⊢
    rw [ih] at hr
    have hi : m + 3 - 2 = m + 1 := by omega
    rw [hi]
    linear_combination hr - hq

/-- The first row realizes the conjecture's convention `F(-1) = 1`. -/
theorem schulte_conjecture_one : altRowSum 1 = 1 := by
  norm_num [altRowSum, denominator]

#print axioms altRowSum_succ_sub
#print axioms fib_cassini_two
#print axioms schulte_conjecture
#print axioms schulte_conjecture_one

end D5.S1.Recurrence.Parity.HarmonicTriangleAlternatingRowSums

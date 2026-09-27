/- GID: D5/S3/Combinatorics/LatticeReturnsRecurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LatticeReturnsRecurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves R. J. Mathar's 2012 recurrence conjecture for OEIS A068551, a(n) = 4^n - binomial(2n, n), the total number of returns to the axis in all +-1 lattice paths from the origin to (2n, 0): n a(n) + 2(3 - 4n) a(n-1) + 8(2n - 3) a(n-2) = 0 for n >= 2. -/

/-
proof_shape: result: bind-only
escape_witness: none; every atomic fact is an instance of a pinned Mathlib lemma
  (`Nat.centralBinom_eq_two_mul_choose`, `Nat.succ_mul_centralBinom_succ` at `m` and `m + 1`,
  `pow_succ`), combined by `push_cast` and `linear_combination`
admission_basis: open-problem-resolution (issue #10754), which admits a bind-only settlement
  of an external named open problem
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LatticeReturnsRecurrence

/-- A068551: `a(n) = 4^n - binomial(2n, n)`. -/
def a (n : ℕ) : ℤ := 4 ^ n - ((2 * n).choose n : ℤ)

/-- Mathar's conjecture (OEIS A068551, formula field, 2012). -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (n : ℤ) * a n + 2 * (3 - 4 * n) * a (n - 1) + 8 * (2 * n - 3) * a (n - 2) = 0

/-- The conjecture holds. -/
theorem result : claim := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have c0 : ((2 * m).choose m : ℤ) = (m.centralBinom : ℤ) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
  have c1 : ((2 * (m + 1)).choose (m + 1) : ℤ) = ((m + 1).centralBinom : ℤ) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
  have c2 : ((2 * (m + 2)).choose (m + 2) : ℤ) = ((m + 2).centralBinom : ℤ) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
  have q1 : ((m : ℤ) + 1) * ((m + 1).centralBinom : ℤ) =
      2 * (2 * m + 1) * (m.centralBinom : ℤ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ m
  have q2 : ((m : ℤ) + 2) * ((m + 2).centralBinom : ℤ) =
      2 * (2 * m + 3) * ((m + 1).centralBinom : ℤ) := by
    have h := Nat.succ_mul_centralBinom_succ (m + 1)
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring] at h
    exact_mod_cast h
  simp only [a, show m + 2 - 1 = m + 1 from rfl, show m + 2 - 2 = m from rfl, c0, c1, c2]
  push_cast
  linear_combination -q2 + 4 * q1 + ((m : ℤ) + 2) * (pow_succ (4 : ℤ) (m + 1)) -
    2 * (2 * ((m : ℤ) + 2) - 3) * (pow_succ (4 : ℤ) m)

end D5.S3.Combinatorics.LatticeReturnsRecurrence

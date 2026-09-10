/- GID: D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/FactorialQuotientRecurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Positivity and triple-product cancellation prove Mathar's recurrence and integrality. -/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The factorial-quotient recurrence of OEIS A372991

The sequence is defined over the rationals so division does not presuppose
integrality. Positivity makes cancellation of consecutive triple products
legitimate, giving Mathar's conjectured recurrence for every index at least
three. Integrality is then a consequence of that recurrence.

All results are unbounded symbolic statements; no finite regression declaration
is included. The dependency direction is `a_integral` -> `mathar_recurrence`
-> `triple_product` -> `a_pos` -> `a`.
-/

namespace D5.S1.Recurrence.Invariants.FactorialQuotientRecurrence

/-- OEIS A372991: "a(n) = (2n)!/(a(n-1)*a(n-2)), where a(0)=1, a(1) = 1."
The factorial is cast to `ℚ`, and the quotient is rational division. -/
def a : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | n + 2 => (Nat.factorial (2 * (n + 2)) : ℚ) / (a (n + 1) * a n)

/-- Every term of the factorial-quotient sequence is strictly positive. -/
theorem a_pos (n : ℕ) : 0 < a n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [a]
  | one => norm_num [a]
  | more n hn hn1 =>
    rw [a]
    exact div_pos (by exact_mod_cast Nat.factorial_pos (2 * (n + 2))) (mul_pos hn1 hn)

/-- Three consecutive terms multiply to the factorial in the defining recurrence. -/
theorem triple_product (n : ℕ) :
    a (n + 2) * a (n + 1) * a n = (Nat.factorial (2 * (n + 2)) : ℚ) := by
  rw [a, mul_assoc, div_mul_cancel₀ _ (mul_ne_zero (ne_of_gt (a_pos (n + 1)))
    (ne_of_gt (a_pos n)))]

/-- Cancel the two shared positive factors in consecutive triple products. -/
private theorem recurrence_step (n : ℕ) :
    a (n + 3) = (2 * (n + 3) : ℚ) * (2 * (n + 3) - 1) * a n := by
  have hfac : (Nat.factorial (2 * (n + 3)) : ℚ) =
      (2 * (n + 3) : ℚ) * (2 * (n + 3) - 1) *
        (Nat.factorial (2 * (n + 2)) : ℚ) := by
    have hindex : 2 * (n + 3) = (2 * (n + 2) + 1) + 1 := by omega
    rw [hindex, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  apply mul_right_cancel₀ (mul_ne_zero (ne_of_gt (a_pos (n + 2)))
    (ne_of_gt (a_pos (n + 1))))
  calc
    a (n + 3) * (a (n + 2) * a (n + 1)) =
        (Nat.factorial (2 * (n + 3)) : ℚ) := by
      simpa only [Nat.add_assoc, mul_assoc] using triple_product (n + 1)
    _ = (2 * (n + 3) : ℚ) * (2 * (n + 3) - 1) *
        (a (n + 2) * a (n + 1) * a n) := by rw [triple_product, hfac]
    _ = ((2 * (n + 3) : ℚ) * (2 * (n + 3) - 1) * a n) *
        (a (n + 2) * a (n + 1)) := by ring

/-- Mathar's conjecture for OEIS A372991, for every `n ≥ 3`.
Here `n` is cast to `ℚ` before multiplication and subtraction in the coefficient
`2 * n * (2 * n - 1)`; subtraction in the index `n - 3` is natural subtraction. -/
theorem mathar_recurrence (n : ℕ) (hn : 3 ≤ n) :
    a n = 2 * (n : ℚ) * (2 * (n : ℚ) - 1) * a (n - 3) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm, Nat.cast_add] using recurrence_step m

/-- Every rational term of OEIS A372991 is the cast of a natural number. -/
theorem a_integral (n : ℕ) : ∃ k : ℕ, a n = k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : 3 ≤ n
    · obtain ⟨k, hk⟩ := ih (n - 3) (by omega)
      refine ⟨2 * n * (2 * n - 1) * k, ?_⟩
      rw [mathar_recurrence n hn, hk]
      have htwo : 1 ≤ 2 * n := by omega
      push_cast [Nat.cast_sub htwo]
      ring
    · have hsmall : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases hsmall with rfl | rfl | rfl
      · exact ⟨1, by norm_num [a]⟩
      · exact ⟨1, by norm_num [a]⟩
      · exact ⟨24, by norm_num [a, Nat.factorial]⟩

#print axioms a_pos
#print axioms triple_product
#print axioms mathar_recurrence
#print axioms a_integral

end D5.S1.Recurrence.Invariants.FactorialQuotientRecurrence

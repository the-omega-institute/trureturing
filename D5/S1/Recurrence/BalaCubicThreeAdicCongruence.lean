/- GID: D5/S1/Recurrence/BalaCubicThreeAdicCongruence
   generality: G
   mirror-B: D5/B/S1/Recurrence/BalaCubicThreeAdicCongruence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Bala's cubic recurrence has the conjectured growing power-of-three divisor. -/

import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.Ring

namespace D5.S1.Recurrence.BalaCubicThreeAdicCongruence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A002000 by its %N recurrence: a(n+1) = a(n)*(a(n)^2 - 3) with a(0) = 7. -/
def a : ℕ → ℤ
  | 0 => 7
  | n + 1 => a n * (a n ^ 2 - 3)

private theorem a_plus_two (n : ℕ) :
    (3 : ℤ) ^ (2 * n + 2) ∣ a n + 2 := by
  induction n with
  | zero => norm_num [a]
  | succ n ih =>
    have hthree : (3 : ℤ) ∣ a n + 2 :=
      (dvd_pow_self (3 : ℤ) (by omega : 2 * n + 2 ≠ 0)).trans ih
    have hminus : (3 : ℤ) ∣ a n - 1 := by
      simpa only [show a n + 2 - 3 = a n - 1 by ring] using
        dvd_sub hthree (dvd_refl (3 : ℤ))
    rw [show a (n + 1) + 2 = (a n - 1) ^ 2 * (a n + 2) by
      simp only [a]
      ring]
    simpa only [← pow_add,
      show 2 + (2 * n + 2) = 2 * (n + 1) + 2 by omega] using
      mul_dvd_mul (pow_dvd_pow_of_dvd hminus 2) ih

/-- Bala's A002000 congruence, for every pair of natural indices r ≤ n. -/
theorem result (n r : ℕ) (hr : r ≤ n) :
    (3 : ℤ) ^ (n + r + 2) ∣ a (n + 1) - a n := by
  let q : ℤ := Classical.choose (a_plus_two n)
  have hq : a n + 2 = (3 : ℤ) ^ (2 * n + 2) * q :=
    Classical.choose_spec (a_plus_two n)
  have hstrong : (3 : ℤ) ^ (2 * n + 2) ∣ a (n + 1) - a n := by
    refine ⟨a n * (a n - 2) * q, ?_⟩
    rw [show a (n + 1) - a n = a n * (a n - 2) * (a n + 2) by
      simp only [a]
      ring, hq]
    ring
  exact (pow_dvd_pow (3 : ℤ) (by omega : n + r + 2 ≤ 2 * n + 2)).trans hstrong

end D5.S1.Recurrence.BalaCubicThreeAdicCongruence

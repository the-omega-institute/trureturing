/- GID: D5/S1/Recurrence/BalaLucasFiveAdicCongruence
   generality: G
   mirror-B: D5/B/S1/Recurrence/BalaLucasFiveAdicCongruence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Bala's quintic recurrence has the conjectured growing power-of-five divisor. -/

import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.Ring

namespace D5.S1.Recurrence.BalaLucasFiveAdicCongruence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A144837 by Bala's recurrence, with a(0) = 1 = Lucas(5^0), so a(1) = 11 = A144837(1). -/
def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => a n ^ 5 + 5 * a n ^ 3 + 5 * a n

private theorem a_sq_plus_four (n : ℕ) :
    (5 : ℤ) ^ (2 * n + 1) ∣ a n ^ 2 + 4 := by
  induction n with
  | zero => norm_num [a]
  | succ n ih =>
    have hfive : (5 : ℤ) ∣ a n ^ 2 + 4 :=
      (dvd_pow_self (5 : ℤ) (by omega : 2 * n + 1 ≠ 0)).trans ih
    have hfactor : (5 : ℤ) ∣ a n ^ 4 + 3 * a n ^ 2 + 1 := by
      rw [show a n ^ 4 + 3 * a n ^ 2 + 1 =
        (a n ^ 2 + 4) * (a n ^ 2 - 1) + 5 by ring]
      exact dvd_add (dvd_mul_of_dvd_left hfive _) (dvd_refl (5 : ℤ))
    rw [show a (n + 1) ^ 2 + 4 =
      (a n ^ 4 + 3 * a n ^ 2 + 1) ^ 2 * (a n ^ 2 + 4) by
      simp only [a]
      ring]
    simpa only [← pow_add,
      show 2 + (2 * n + 1) = 2 * (n + 1) + 1 by omega] using
      mul_dvd_mul (pow_dvd_pow_of_dvd hfactor 2) ih

/-- Bala's A144837 conjecture, for all natural indices r ≤ n, including n = 0. -/
theorem result (n r : ℕ) (hr : r ≤ n) :
    (5 : ℤ) ^ (n + r + 1) ∣ a (n + 1) - a n := by
  have hstrong : (5 : ℤ) ^ (2 * n + 1) ∣ a (n + 1) - a n := by
    obtain ⟨q, hq⟩ := a_sq_plus_four n
    refine ⟨a n * (a n ^ 2 + 1) * q, ?_⟩
    rw [show a (n + 1) - a n = a n * (a n ^ 2 + 1) * (a n ^ 2 + 4) by
      simp only [a]
      ring, hq]
    ring
  exact (pow_dvd_pow (5 : ℤ) (by omega : n + r + 1 ≤ 2 * n + 1)).trans hstrong

end D5.S1.Recurrence.BalaLucasFiveAdicCongruence

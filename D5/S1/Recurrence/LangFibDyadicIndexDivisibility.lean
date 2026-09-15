/- GID: D5/S1/Recurrence/LangFibDyadicIndexDivisibility
   generality: G
   mirror-B: D5/B/S1/Recurrence/LangFibDyadicIndexDivisibility
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Powers of two divide Fibonacci numbers at Lang's dyadic indices. -/

import Mathlib.Data.Nat.Fib.Basic

namespace D5.S1.Recurrence.LangFibDyadicIndexDivisibility

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem result (n m : ℕ) (hn : 3 ≤ n) :
    2 ^ n ∣ Nat.fib (2 ^ (n - 2) * 3 * m) := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num only [Nat.reduceSub, Nat.reducePow, Nat.reduceMul]
      simpa only [show Nat.fib 6 = 8 by decide] using
        Nat.fib_dvd 6 (6 * m) (dvd_mul_right 6 m)
  | succ n hn ih =>
      have hindex : 2 ^ (n + 1 - 2) * 3 * m =
          2 * (2 ^ (n - 2) * 3 * m) := by
        rw [show n + 1 - 2 = (n - 2) + 1 by omega, pow_succ]
        ring
      rw [hindex, Nat.fib_two_mul, pow_succ]
      apply mul_dvd_mul ih
      have heven : 2 ∣ Nat.fib (2 ^ (n - 2) * 3 * m) := by
        apply dvd_trans (b := 2 ^ n) _ ih
        simpa only [pow_one] using pow_dvd_pow 2 (show 1 ≤ n by omega)
      exact Nat.dvd_sub (dvd_mul_right 2 _) heven

end D5.S1.Recurrence.LangFibDyadicIndexDivisibility

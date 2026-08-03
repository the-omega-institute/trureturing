/- GID: D5/S1/Recurrence/GoldenFibDivisibility
   generality: I
   mirror-B: D5/B/S1/Recurrence/GoldenFibDivisibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fibonacci divisibility reflects divisibility of indices from index three onward. -/

import Mathlib

/- Provenance: Native proof over pinned mathlib. -/

namespace D5.S1.Recurrence.GoldenFibDivisibility

/-- For indices at least three, Fibonacci divisibility is exactly divisibility
of indices. The single obstruction is `a = 2`: there `fib 2 = 1` divides every
`fib b` while `2 ∣ b` can fail (e.g. `b = 3`). The equivalence in fact also
holds at `a = 0` and `a = 1`, so `3 ≤ a` is simply the minimal uniform lower
bound that excludes the `a = 2` gap. -/
theorem fib_dvd_iff (a b : ℕ) (ha : 3 ≤ a) : Nat.fib a ∣ Nat.fib b ↔ a ∣ b := by
  constructor
  · intro hdvd
    have hfib_gcd : Nat.fib (Nat.gcd a b) = Nat.fib a := by
      rw [Nat.fib_gcd, Nat.gcd_eq_left_iff_dvd.mpr hdvd]
    have hgcd_eq : Nat.gcd a b = a := by
      by_contra hne
      have hgcd_lt : Nat.gcd a b < a :=
        Nat.lt_of_le_of_ne (Nat.gcd_le_left b (by omega)) hne
      have hfib_lt : Nat.fib (Nat.gcd a b) < Nat.fib a := by
        calc
          Nat.fib (Nat.gcd a b) ≤ Nat.fib (a - 1) :=
            Nat.fib_mono (by omega)
          _ < Nat.fib a := by
            rw [show a = (a - 1) + 1 by omega]
            exact Nat.fib_lt_fib_succ (by omega)
      exact (Nat.ne_of_lt hfib_lt) hfib_gcd
    exact Nat.gcd_eq_left_iff_dvd.mp hgcd_eq
  · exact Nat.fib_dvd a b

end D5.S1.Recurrence.GoldenFibDivisibility

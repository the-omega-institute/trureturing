/- GID: D5/S3/Arith/Congruence/CaceresGcdFactorialPowerPrimeCriterion
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/CaceresGcdFactorialPowerPrimeCriterion
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Caceres' A308090 gcd-factorial-power primality criterion. -/

import Mathlib.Data.Nat.Prime.Factorial

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.CaceresGcdFactorialPowerPrimeCriterion

/-- OEIS A308090: the gcd of the two factorial-shifted powers and `n + 1`. -/
def a (n : ℕ) : ℕ :=
  Nat.gcd (Nat.gcd (2 ^ n + n.factorial) (3 ^ n + n.factorial)) (n + 1)

/-- Caceres' criterion: if `a n = n + 1` for positive `n`, then `n + 1` is prime. -/
theorem result (n : ℕ) (hn : 0 < n) (h : a n = n + 1) : (n + 1).Prime := by
  have hmX : n + 1 ∣ 2 ^ n + n.factorial := by
    have hmG : n + 1 ∣ a n := by simp [h]
    exact hmG.trans
      ((Nat.gcd_dvd_left (Nat.gcd (2 ^ n + n.factorial) (3 ^ n + n.factorial))
          (n + 1)).trans
        (Nat.gcd_dvd_left (2 ^ n + n.factorial) (3 ^ n + n.factorial)))
  have hmY : n + 1 ∣ 3 ^ n + n.factorial := by
    have hmG : n + 1 ∣ a n := by simp [h]
    exact hmG.trans
      ((Nat.gcd_dvd_left (Nat.gcd (2 ^ n + n.factorial) (3 ^ n + n.factorial))
          (n + 1)).trans
        (Nat.gcd_dvd_right (2 ^ n + n.factorial) (3 ^ n + n.factorial)))
  by_contra hnp
  obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd (by omega : n + 1 ≠ 1)
  have hq_ne : q ≠ n + 1 := by
    intro hEq
    apply hnp
    rw [← hEq]
    exact hq
  have hq_lt : q < n + 1 :=
    lt_of_le_of_ne (Nat.le_of_dvd (by omega) hqm) hq_ne
  have hq_le : q ≤ n := by omega
  have hqfac : q ∣ n.factorial := Nat.dvd_factorial hq.pos hq_le
  have hqX : q ∣ 2 ^ n + n.factorial := hqm.trans hmX
  have hqY : q ∣ 3 ^ n + n.factorial := hqm.trans hmY
  have hqpow2 : q ∣ 2 ^ n := (Nat.dvd_add_left hqfac).mp hqX
  have hqpow3 : q ∣ 3 ^ n := (Nat.dvd_add_left hqfac).mp hqY
  have hq2 : q ∣ 2 := hq.dvd_of_dvd_pow hqpow2
  have hq3 : q ∣ 3 := hq.dvd_of_dvd_pow hqpow3
  have hqone : q ∣ 1 := by
    simpa using Nat.dvd_gcd hq2 hq3
  exact hq.not_dvd_one hqone

end D5.S3.Arith.Congruence.CaceresGcdFactorialPowerPrimeCriterion

/- GID: D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/StirlingTransformTotientPeriod
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Weighted Stirling transforms have totient periods, proving A064618 and A004123. -/

import D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod

/-!
# Totient periods for weighted Stirling transforms

For every integer weight, the factorial-weighted Stirling transform has period
`Nat.totient m` modulo each positive modulus `m`, at indices `n ≥ m`.
The two specializations are the finite OEIS formulas recorded in
`Library/Recurrence/bala2018a064618.md`: A064618 has weight `k!`, and
A004123 has weight `2^k` with its offset-one index shifted to `n - 1`.
Neither the onset nor the period is asserted to be minimal. The broader
A004123 conjecture about every e.g.f. `G(exp(x) - 1)` is not claimed here.

This is a sibling of `AlternatingWeightStirlingPrimePeriod`, not an instance:
its summand has no extra `k^n`, and the modulus need not be prime. The fixed
factorial window and the frozen inclusion-exclusion identity reduce the
problem to powers. For each prime power dividing the modulus, unit bases
use Euler's theorem and non-unit bases vanish once the exponent is large
enough. Prime-power divisibility then combines these local congruences.

Freeze prerequisite:
`D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod`, statement_id
`sha256:de3301b051609b0cfd4822db18707fa5d6b43e7a78e550dda3911b35c172da11`.
-/

open Finset

namespace D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod

/-- The factorial-weighted Stirling transform of an arbitrary integer weight. -/
def T (w : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), w k * (k.factorial : ℤ) * (Nat.stirlingSecond n k : ℤ)

/-- Reduction to a fixed modulus-sized window, valid also at index zero. -/
theorem T_window (w : ℕ → ℤ) (m n : ℕ) (hm : 0 < m) :
    (T w n : ZMod m) = ∑ k ∈ range m,
      ((w k * (k.factorial : ℤ) * (Nat.stirlingSecond n k : ℤ) : ℤ) : ZMod m) := by
  simp only [T, Int.cast_sum]
  rcases le_total (n + 1) m with h | h
  · apply sum_subset (range_mono h)
    intro k _ hk
    have hnk : n < k := by simp only [mem_range] at hk; omega
    simp [Nat.stirlingSecond_eq_zero_of_lt hnk]
  · symm
    apply sum_subset (range_mono h)
    intro k _ hk
    have hmk : m ≤ k := by simpa only [mem_range, not_lt] using hk
    have hf : (k.factorial : ZMod m) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_factorial hm hmk)
    simp only [Int.cast_mul, Int.cast_natCast, hf, mul_zero, zero_mul]

/-- Inclusion-exclusion gives exponential coefficients independent of `n`. -/
theorem T_exponential_sum (w : ℕ → ℤ) (m n : ℕ) (hm : 0 < m) :
    (T w n : ZMod m) = ∑ k ∈ range m, ∑ j ∈ range (k + 1),
      (w k : ZMod m) * ((-1 : ZMod m) ^ (k - j) * (Nat.choose k j : ZMod m)) *
        (j : ZMod m) ^ n := by
  rw [T_window w m n hm]
  apply sum_congr rfl
  intro k hk
  have hi := congrArg (Int.castRingHom (ZMod m))
    (D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion n k)
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast] at hi
  push_cast
  rw [mul_assoc, hi, mul_sum]
  apply sum_congr rfl
  intro j hj
  ring

private theorem prime_power_step (j m n p e : ℕ) (hm : 0 < m)
    (hn : m ≤ n) (hp : p.Prime) (he : p ^ e ∣ m) :
    Nat.ModEq (p ^ e) (j ^ (n + m.totient)) (j ^ n) := by
  by_cases hj : p ∣ j
  · have hen : e ≤ n :=
      (Nat.lt_pow_self hp.one_lt).le.trans ((Nat.le_of_dvd hm he).trans hn)
    have hz (r : ℕ) (hr : e ≤ r) : Nat.ModEq (p ^ e) (j ^ r) 0 :=
      Nat.modEq_zero_iff_dvd.mpr
        ((pow_dvd_pow_of_dvd hj e).trans (pow_dvd_pow j hr))
    exact (hz _ (by omega)).trans (hz n hen).symm
  · have hc : j.Coprime (p ^ e) := (hp.coprime_iff_not_dvd.mpr hj).symm.pow_right e
    obtain ⟨t, ht⟩ := Nat.totient_dvd_of_dvd he
    have hu := (Nat.ModEq.pow_totient hc).pow t
    rw [← pow_mul, ← ht, one_pow] at hu
    simpa only [pow_add, mul_one] using hu.mul_left (j ^ n)

/-- Euler's theorem for units and vanishing for non-units, combined over prime powers. -/
theorem pow_add_totient (j m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (j : ZMod m) ^ (n + Nat.totient m) = (j : ZMod m) ^ n := by
  rw [← Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff,
    Nat.modEq_iff_dvd, ← Int.dvd_natAbs, Int.natCast_dvd_natCast]
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p e hp he
  have h := prime_power_step j m n p e hm hn hp he
  rwa [Nat.modEq_iff_dvd, ← Int.dvd_natAbs, Int.natCast_dvd_natCast] at h

/-- Every integer weight has totient period modulo `m` from index `m` onward. -/
theorem stirling_transform_totient_period (w : ℕ → ℤ) (m n : ℕ)
    (hm : 0 < m) (hn : m ≤ n) :
    (T w (n + Nat.totient m) : ZMod m) = (T w n : ZMod m) := by
  rw [T_exponential_sum w m _ hm, T_exponential_sum w m _ hm]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro j hj
  rw [pow_add_totient j m n hm hn]

/-- Bala's A064618 conjecture for the finite formula `∑ k≤n, (k!)² S(n,k)`. -/
theorem bala_conjecture_a064618 (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (T (fun k => (k.factorial : ℤ)) (n + Nat.totient m) : ZMod m) =
      (T (fun k => (k.factorial : ℤ)) n : ZMod m) := by
  exact stirling_transform_totient_period _ m n hm hn

/-- Bala's A004123 conjecture in the entry's own offset-one indexing:
`a(n) = T (fun k => 2^k) (n-1)`, with the proved onset `n ≥ m+1`. -/
theorem bala_conjecture_a004123 (m n : ℕ) (hm : 0 < m) (hn : m + 1 ≤ n) :
    (T (fun k => (2 : ℤ) ^ k) (n + Nat.totient m - 1) : ZMod m) =
      (T (fun k => (2 : ℤ) ^ k) (n - 1) : ZMod m) := by
  rw [show n + Nat.totient m - 1 = (n - 1) + Nat.totient m by omega]
  exact stirling_transform_totient_period _ m (n - 1) hm (by omega)

#print axioms T
#print axioms T_window
#print axioms T_exponential_sum
#print axioms pow_add_totient
#print axioms stirling_transform_totient_period
#print axioms bala_conjecture_a064618
#print axioms bala_conjecture_a004123

end D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod

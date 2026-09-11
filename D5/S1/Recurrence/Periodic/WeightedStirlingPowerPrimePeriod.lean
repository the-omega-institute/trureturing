/- GID: D5/S1/Recurrence/Periodic/WeightedStirlingPowerPrimePeriod
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/WeightedStirlingPowerPrimePeriod
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A weighted prime window and Fermat prove Bala's A338040 periodicity conjecture. -/

import D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod

/-!
# Prime periods of the weighted Stirling power sum

OEIS A338040 defines its sequence by the e.g.f.
`Sum_{j>=0} 4^j * (exp(j*x) - 1)^j` and states the finite FORMULA used
below. The formal definition uses that finite formula; the e.g.f. identity
itself is not proved here. The period `p - 1` need not be minimal.

Freeze prerequisite:
`D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod`, statement_id
`sha256:de3301b051609b0cfd4822db18707fa5d6b43e7a78e550dda3911b35c172da11`.
-/

open Finset

namespace D5.S1.Recurrence.Periodic.WeightedStirlingPowerPrimePeriod

/-- The offset-zero finite FORMULA in OEIS A338040, whose NAME defines the e.g.f. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), 4 ^ k * k ^ n * k.factorial * Nat.stirlingSecond n k

/-- The weighted sum reduces to a fixed prime-sized window, also at index zero. -/
theorem a_eq_window (p n : ℕ) (hp : p.Prime) :
    (a n : ZMod p) =
      ∑ k ∈ range p,
        ((4 ^ k * k ^ n * k.factorial * Nat.stirlingSecond n k : ℕ) : ZMod p) := by
  simp only [a, Nat.cast_sum]
  rcases le_total (n + 1) p with h | h
  · apply sum_subset (range_mono h)
    intro k _ hk
    have hnk : n < k := by simp only [mem_range] at hk; omega
    simp [Nat.stirlingSecond_eq_zero_of_lt hnk]
  · symm
    apply sum_subset (range_mono h)
    intro k _ hk
    have hpk : p ≤ k := by simpa only [mem_range, not_lt] using hk
    have hf : (k.factorial : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_factorial hp.pos hpk)
    simp only [Nat.cast_mul, hf, mul_zero, zero_mul]

private theorem a_eq_double_sum (p n : ℕ) (hp : p.Prime) :
    (a n : ZMod p) = ∑ k ∈ range p, ∑ j ∈ range (k + 1),
      (4 : ZMod p) ^ k * ((-1 : ZMod p) ^ (k - j) * (Nat.choose k j : ZMod p)) *
        ((k : ZMod p) * (j : ZMod p)) ^ n := by
  rw [a_eq_window p n hp]
  apply sum_congr rfl
  intro k hk
  have hi := congrArg (Int.castRingHom (ZMod p))
    (D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion n k)
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast] at hi
  push_cast
  rw [mul_assoc ((4 : ZMod p) ^ k * (k : ZMod p) ^ n), hi, mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [mul_pow]
  ring

private theorem power_period (p : ℕ) (hp : p.Prime) (x : ZMod p)
    (n : ℕ) (hn : 1 ≤ n) : x ^ (n + (p - 1)) = x ^ n := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hx : x = 0
  · simp [hx, show n ≠ 0 by omega]
  · rw [pow_add, ZMod.pow_card_sub_one_eq_one hx, mul_one]

/-- Bala's A338040 conjecture: `p - 1` is a period modulo each prime at positive indices. -/
theorem bala_conjecture (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    (a (n + (p - 1)) : ZMod p) = a n := by
  rw [a_eq_double_sum p _ hp, a_eq_double_sum p _ hp]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro j hj
  rw [power_period p hp _ n hn]

/-- Every nonnegative multiple of the period preserves every positive-index term. -/
theorem bala_conjecture_periodic (p : ℕ) (hp : p.Prime) (n m : ℕ) (hn : 1 ≤ n) :
    (a (n + m * (p - 1)) : ZMod p) = a n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, bala_conjecture p hp _ (by omega), ih]

#print axioms a_eq_window
#print axioms bala_conjecture
#print axioms bala_conjecture_periodic

end D5.S1.Recurrence.Periodic.WeightedStirlingPowerPrimePeriod

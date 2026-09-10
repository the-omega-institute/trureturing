/- GID: D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integer-weight Stirling power sums have prime periods, proving Bala's A220181 claim. -/

import D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod

/-!
# Prime periods for arbitrary integer weights

For every weight `w : ℕ → ℤ`, the Stirling power-factorial sum has period
`p - 1` modulo each prime `p` at positive indices. A fixed prime-sized window
and inclusion-exclusion give a public exponential-sum representation whose
coefficients are independent of the sequence index.

The named instances are A122399 (`w = 1`, already frozen), A338040
(`w k = 4 ^ k`, already frozen), and A220181 (`w k = (-1) ^ k`, with the
additional factor `(-1) ^ n`, proved here). The definition of A220181 is
its finite OEIS FORMULA. The NAME gives the e.g.f.
`Sum_{n>=0} (1 - exp(-n*x))^n`; that e.g.f. identity is not formalized here.
The period is not asserted to be minimal.

A literature check on 2026-09-09 found Bala's identical conjecture recorded
without a proof note on A224899, A221077 and A195415. Their e.g.f. shapes are
not of this weighted form; no result about those three entries is claimed here.

Freeze prerequisite:
`D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod`, statement_id
`sha256:de3301b051609b0cfd4822db18707fa5d6b43e7a78e550dda3911b35c172da11`.
-/

open Finset

namespace D5.S1.Recurrence.Periodic.AlternatingWeightStirlingPrimePeriod

/-- The Stirling power-factorial sum with an arbitrary integer weight. -/
def aw (w : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), w k * (k : ℤ) ^ n * (k.factorial : ℤ) *
    (Nat.stirlingSecond n k : ℤ)

/-- Reduction to a fixed prime-sized window, including index zero. -/
theorem aw_window (w : ℕ → ℤ) (p n : ℕ) (hp : p.Prime) :
    (aw w n : ZMod p) = ∑ k ∈ range p,
      ((w k * (k : ℤ) ^ n * (k.factorial : ℤ) *
        (Nat.stirlingSecond n k : ℤ) : ℤ) : ZMod p) := by
  simp only [aw, Int.cast_sum]
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
    simp only [Int.cast_mul, Int.cast_natCast, hf, mul_zero, zero_mul]

/-- The exponential-sum coefficients depend on the weight and prime, not on `n`. -/
theorem aw_exponential_sum (w : ℕ → ℤ) (p n : ℕ) (hp : p.Prime) :
    (aw w n : ZMod p) = ∑ k ∈ range p, ∑ j ∈ range (k + 1),
      (w k : ZMod p) * ((-1 : ZMod p) ^ (k - j) * (Nat.choose k j : ZMod p)) *
        ((k : ZMod p) * (j : ZMod p)) ^ n := by
  rw [aw_window w p n hp]
  apply sum_congr rfl
  intro k hk
  have hi := congrArg (Int.castRingHom (ZMod p))
    (D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion n k)
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast] at hi
  push_cast
  rw [mul_assoc ((w k : ZMod p) * (k : ZMod p) ^ n), hi, mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [mul_pow]
  ring

/-- Positive powers have prime period, including the zero base. -/
theorem pow_add_pred_prime {p : ℕ} (hp : p.Prime) (x : ZMod p)
    (n : ℕ) (hn : 1 ≤ n) : x ^ (n + (p - 1)) = x ^ n := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hx : x = 0
  · simp [hx, show n ≠ 0 by omega]
  · rw [pow_add, ZMod.pow_card_sub_one_eq_one hx, mul_one]

/-- Every integer weight gives period `p - 1` modulo a prime at positive indices. -/
theorem aw_prime_period (w : ℕ → ℤ) (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) :
    (aw w (n + (p - 1)) : ZMod p) = (aw w n : ZMod p) := by
  rw [aw_exponential_sum w p _ hp, aw_exponential_sum w p _ hp]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro j hj
  rw [pow_add_pred_prime hp _ n hn]

/-- Every nonnegative multiple of the period preserves the weighted sum. -/
theorem aw_prime_period_multiple (w : ℕ → ℤ) (p n m : ℕ)
    (hp : p.Prime) (hn : 1 ≤ n) :
    (aw w (n + m * (p - 1)) : ZMod p) = (aw w n : ZMod p) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, aw_prime_period w p _ hp (by omega), ih]

/-- The offset-zero finite FORMULA of OEIS A220181. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (-1) ^ (n - k) * (k : ℤ) ^ n * (k.factorial : ℤ) *
    (Nat.stirlingSecond n k : ℤ)

/-- The OEIS finite formula is the signed alternating-weight sum. -/
theorem a_eq_alternating (n : ℕ) : a n = (-1) ^ n * aw (fun k => (-1) ^ k) n := by
  unfold a aw
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using mem_range.mp hk
  have hs : (-1 : ℤ) ^ n * (-1) ^ k = (-1) ^ (n - k) := by
    calc
      _ = (-1) ^ (n - k) * ((-1) ^ k * (-1) ^ k) := by
        rw [← mul_assoc, ← pow_add (-1 : ℤ) (n - k) k, Nat.sub_add_cancel hkn]
      _ = _ := by rw [← pow_add, ← two_mul, pow_mul]; simp
  rw [← hs]
  ring

/-- Bala's A220181 conjecture, with period not necessarily minimal. -/
theorem bala_conjecture (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) :
    (a (n + (p - 1)) : ZMod p) = (a n : ZMod p) := by
  rw [a_eq_alternating, a_eq_alternating]
  push_cast
  rw [aw_prime_period _ p n hp hn]
  by_cases hp2 : p = 2
  · subst p
    have hs : (-1 : ZMod 2) = 1 := by decide
    simp only [hs, one_pow]
  · rw [pow_add, (hp.even_sub_one hp2).neg_one_pow, mul_one]

/-- Every nonnegative multiple of the prime period preserves A220181. -/
theorem bala_conjecture_periodic (p n m : ℕ) (hp : p.Prime) (hn : 1 ≤ n) :
    (a (n + m * (p - 1)) : ZMod p) = (a n : ZMod p) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, bala_conjecture p _ hp (by omega), ih]

#print axioms aw
#print axioms aw_window
#print axioms aw_exponential_sum
#print axioms pow_add_pred_prime
#print axioms aw_prime_period
#print axioms aw_prime_period_multiple
#print axioms a
#print axioms a_eq_alternating
#print axioms bala_conjecture
#print axioms bala_conjecture_periodic

end D5.S1.Recurrence.Periodic.AlternatingWeightStirlingPrimePeriod

/- GID: D5/S1/Digit/KurkovWeightProductBinomial
   generality: G
   mirror-B: D5/B/S1/Digit/KurkovWeightProductBinomial
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Binary-weight products satisfy Kurkov's binomial identity for all natural indices. -/

import D5.S1.Digit.DyadicRowPolynomialRecurrence

/-! A284005 multiplies one plus the binary weight along successive binary
shifts. Its NAME gives the recurrence for n > 1; the data fixes a(1) = 2,
which is also the value obtained by extending the recurrence to every
positive index. Only Kurkov's April 24, 2023 binomial identity is asserted.
The bit-flip recursion, the mod-2 transform of A329369, and the divisor-count
representation via A283477 are outside this statement.

All declarations describe functions on all naturals or symbolic induction
identities. None is a bounded enumeration, checker, numeric reduction, or
certified finite instance; hence `utility: none`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.KurkovWeightProductBinomial

open D5.S1.Digit.DyadicRowPolynomialRecurrence (wt)

/-- A284005 by its NAME recurrence, with a(0) = 1 and the data value a(1) = 2. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => (1 + wt (n + 1)) * a ((n + 1) / 2)

/-- Kurkov's binomial identity for A284005 at all natural indices. -/
theorem result (m n : ℕ) :
    a (2 ^ m * (2 * n + 1)) =
      ∑ k ∈ Finset.range (m + 2), Nat.choose (m + 1) k * a (2 ^ k * n) := by
  have a_two_pow_mul : ∀ (k n : ℕ), a (2 ^ k * n) = (1 + wt n) ^ k * a n := by
    intro k n
    have wt_zero : wt 0 = 0 := by simp [wt]
    have wt_two_pow_mul (k n : ℕ) : wt (2 ^ k * n) = wt n := by
      by_cases hn : n = 0
      · simp [hn]
      · unfold wt
        rw [Nat.digits_base_pow_mul (b := 2) (by decide) (Nat.pos_of_ne_zero hn)]
        simp only [List.sum_append, List.sum_replicate, smul_zero, zero_add]
    induction k with
    | zero => simp
    | succ k ih =>
        by_cases hn : n = 0
        · simp [hn, wt_zero]
        · have a_even_pos (n : ℕ) (hn : 0 < n) :
              a (2 * n) = (1 + wt n) * a n := by
            have wt_even (n : ℕ) : wt (2 * n) = wt n := by
              have wt_zero : wt 0 = 0 := by simp [wt]
              by_cases hn : n = 0
              · simp [hn, wt_zero]
              · unfold wt
                rw [Nat.digits_base_mul (b := 2) (by decide) (Nat.pos_of_ne_zero hn)]
                simp
            have hrepr : 2 * n = (2 * n - 1) + 1 := by omega
            rw [hrepr]
            simp only [a]
            have harg : (2 * n - 1) + 1 = 2 * n := by omega
            rw [harg, wt_even]
            have hdiv : (2 * n) / 2 = n := by omega
            rw [hdiv]
          have hx : 0 < 2 ^ k * n := Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero hn)
          rw [pow_succ]
          have harg : 2 ^ k * 2 * n = 2 * (2 ^ k * n) := by ring
          rw [harg, a_even_pos _ hx, wt_two_pow_mul, ih, pow_succ]
          ring
  have a_two_pow_mul_odd : ∀ (m n : ℕ), a (2 ^ m * (2 * n + 1)) = (wt n + 2) ^ (m + 1) * a n := by
    intro m n
    have wt_two_pow_mul (k n : ℕ) : wt (2 ^ k * n) = wt n := by
      by_cases hn : n = 0
      · simp [hn]
      · unfold wt
        rw [Nat.digits_base_pow_mul (b := 2) (by decide) (Nat.pos_of_ne_zero hn)]
        simp only [List.sum_append, List.sum_replicate, smul_zero, zero_add]
    induction m with
    | zero =>
        have a_odd (n : ℕ) :
            a (2 * n + 1) = (wt n + 2) * a n := by
          have wt_odd (n : ℕ) : wt (2 * n + 1) = wt n + 1 := by
            unfold wt
            rw [Nat.add_comm (2 * n), Nat.digits_add 2 (by decide) 1 n (by decide) (by simp)]
            simp [Nat.add_comm]
          simp only [a]
          rw [wt_odd]
          have hdiv : (2 * n + 1) / 2 = n := by omega
          rw [hdiv]
          ring
        simp only [pow_zero, Nat.one_mul, Nat.zero_add]
        simpa only [pow_one] using (a_odd n)
    | succ m ih =>
        have a_even_pos (n : ℕ) (hn : 0 < n) :
            a (2 * n) = (1 + wt n) * a n := by
          have wt_even (n : ℕ) : wt (2 * n) = wt n := by
            have wt_zero : wt 0 = 0 := by simp [wt]
            by_cases hn : n = 0
            · simp [hn, wt_zero]
            · unfold wt
              rw [Nat.digits_base_mul (b := 2) (by decide) (Nat.pos_of_ne_zero hn)]
              simp
          have hrepr : 2 * n = (2 * n - 1) + 1 := by omega
          rw [hrepr]
          simp only [a]
          have harg : (2 * n - 1) + 1 = 2 * n := by omega
          rw [harg, wt_even]
          have hdiv : (2 * n) / 2 = n := by omega
          rw [hdiv]
        have wt_odd (n : ℕ) : wt (2 * n + 1) = wt n + 1 := by
          unfold wt
          rw [Nat.add_comm (2 * n), Nat.digits_add 2 (by decide) 1 n (by decide) (by simp)]
          simp [Nat.add_comm]
        have hx : 0 < 2 ^ m * (2 * n + 1) := by positivity
        rw [pow_succ]
        have harg : 2 ^ m * 2 * (2 * n + 1) = 2 * (2 ^ m * (2 * n + 1)) := by ring
        rw [harg, a_even_pos _ hx, wt_two_pow_mul, wt_odd, ih, pow_succ]
        ring
  rw [a_two_pow_mul_odd]
  have hbase : wt n + 2 = (1 + wt n) + 1 := by omega
  rw [hbase, add_pow]
  simp only [one_pow, Nat.mul_one]
  rw [Finset.sum_mul]
  have hrange : m + 1 + 1 = m + 2 := by omega
  rw [hrange]
  apply Finset.sum_congr rfl
  intro k hk
  rw [a_two_pow_mul k n]
  ac_rfl

end D5.S1.Digit.KurkovWeightProductBinomial

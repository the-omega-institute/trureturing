/- GID: D5/S1/Digit/Admissibility/DigitSumSquareLeastWitness
   generality: G
   mirror-B: D5/B/S1/Digit/Admissibility/DigitSumSquareLeastWitness
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The least simultaneous digit-sum divisor witness in OEIS A389000. -/
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Wu's conjecture for OEIS A389000

The sequence definition is quoted from the orchestrator's reading of OEIS
A389000 on 2026-09-08: the least positive integer k such that n divides both
the base-ten digit sum of k and that of k squared. The conjecture is attributed
to Chai Wah Wu, Oct 01 2025. No network lookup was performed in this sandbox.

The proof derives a sharp leading-digit ceiling, including its equality case,
and uses the mod-nine obstruction to exclude every smaller positive witness.
All results are unbounded symbolic statements; utility is none.
-/

namespace D5.S1.Digit.Admissibility.DigitSumSquareLeastWitness

/-- Base-ten digit sum. -/
def digitSum (x : ℕ) : ℕ := (Nat.digits 10 x).sum

/-- OEIS A389000, quoted from the orchestrator's reading: the least k > 0 with
n ∣ digitSum k ∧ n ∣ digitSum (k^2), when one exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k | 0 < k ∧ n ∣ digitSum k ∧ n ∣ digitSum (k ^ 2)}

private theorem sum_step (x : ℕ) : digitSum x = x % 10 + digitSum (x / 10) := by
  by_cases hx : x = 0
  · simp [hx, digitSum]
  · simpa [digitSum] using congrArg List.sum (Nat.digits_def' (by norm_num : 1 < 10)
      (Nat.pos_of_ne_zero hx))

private theorem sum_small {x : ℕ} (hx : x < 10) : digitSum x = x := by
  rw [sum_step, Nat.mod_eq_of_lt hx, Nat.div_eq_of_lt hx]
  simp [digitSum]

private theorem sum_cons (q r : ℕ) (hr : r < 10) :
    digitSum (10 * q + r) = r + digitSum q := by
  rw [sum_step]
  simp [Nat.add_mod, Nat.add_div, Nat.mod_eq_of_lt hr, Nat.div_eq_of_lt hr,
    Nat.not_le_of_gt hr]

private theorem sum_shift (q d : ℕ) : digitSum (10 ^ d * q) = digitSum q := by
  by_cases hq : q = 0
  · simp [hq, digitSum]
  · simpa [digitSum] using congrArg List.sum
      (Nat.digits_base_pow_mul (b := 10) (k := d) (by norm_num) (Nat.pos_of_ne_zero hq))

private theorem sum_nines (c d : ℕ) (hc : 0 < c) (hc10 : c ≤ 10) :
    digitSum (c * 10 ^ d - 1) = 9 * d + c - 1 := by
  induction d with
  | zero => simpa using (sum_small (x := c - 1) (by omega))
  | succ d ih =>
    have hp : 0 < 10 ^ d := by positivity
    have he : c * 10 ^ (d + 1) - 1 = 10 * (c * 10 ^ d - 1) + 9 := by
      rw [pow_succ, ← mul_assoc]
      have : 0 < c * 10 ^ d := Nat.mul_pos hc hp
      omega
    rw [he, sum_cons _ _ (by norm_num), ih]
    omega

private theorem sum_ceiling (c d x : ℕ) (hc : 0 < c) (hc10 : c ≤ 10)
    (hx : x < c * 10 ^ d) :
    digitSum x ≤ 9 * d + c - 1 ∧
      (digitSum x = 9 * d + c - 1 → x + 1 = c * 10 ^ d) := by
  induction d generalizing x with
  | zero =>
    simp only [pow_zero, mul_one, mul_zero, zero_add] at *
    rw [sum_small (by omega)]
    omega
  | succ d ih =>
    have hq : x / 10 < c * 10 ^ d := by
      apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 10)).2
      simpa [pow_succ, mul_assoc] using hx
    obtain ⟨hb, he⟩ := ih (x / 10) hq
    have hr := Nat.mod_lt x (by norm_num : 0 < 10)
    have hd := Nat.mod_add_div x 10
    rw [sum_step]
    constructor
    · omega
    · intro h
      have hmax : digitSum (x / 10) = 9 * d + c - 1 := by omega
      have := he hmax
      rw [pow_succ, ← mul_assoc]
      omega

private theorem sum_pos {x : ℕ} (hx : 0 < x) : 0 < digitSum x := by
  have hne : Nat.digits 10 x ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have hlast := Nat.getLast_digit_ne_zero 10 (by omega : x ≠ 0)
  have hmem := List.getLast_mem hne
  have hle := List.single_le_sum (fun y _ => Nat.zero_le y) _ hmem
  change 0 < (Nat.digits 10 x).sum
  omega

/-- The candidate has digit sum twice the required divisor. -/
theorem digitSum_witness (m : ℕ) :
    digitSum (2 * 10 ^ (2 * m + 1) - 1) = 2 * (9 * m + 5) := by
  rw [sum_nines 2 _ (by norm_num) (by norm_num)]
  omega

/-- Squaring the candidate preserves its digit sum. -/
theorem digitSum_witness_sq (m : ℕ) :
    digitSum ((2 * 10 ^ (2 * m + 1) - 1) ^ 2) = 2 * (9 * m + 5) := by
  have hp : 0 < 10 ^ (2 * m) := by positivity
  have he : (2 * 10 ^ (2 * m + 1) - 1) ^ 2 =
      10 * (10 ^ (2 * m) * (10 * (4 * 10 ^ (2 * m) - 1) + 6)) + 1 := by
    rw [show 10 ^ (2 * m + 1) = 10 ^ (2 * m) * 10 from pow_succ _ _]
    have h₁ : 1 ≤ 2 * (10 ^ (2 * m) * 10) := by omega
    have h₂ : 1 ≤ 4 * 10 ^ (2 * m) := by omega
    have := Nat.sub_add_cancel h₁
    have := Nat.sub_add_cancel h₂
    nlinarith
  rw [he, sum_cons _ _ (by norm_num), sum_shift,
    sum_cons _ _ (by norm_num), sum_nines 4 _ (by norm_num) (by norm_num)]
  omega

private theorem witness_minimal (m k : ℕ) (hk : 0 < k)
    (hd : (9 * m + 5) ∣ digitSum k)
    (hd₂ : (9 * m + 5) ∣ digitSum (k ^ 2)) :
    2 * 10 ^ (2 * m + 1) - 1 ≤ k := by
  by_contra h
  have hlt : k < 2 * 10 ^ (2 * m + 1) - 1 := by omega
  obtain ⟨hb, he⟩ := sum_ceiling 2 (2 * m + 1) k (by norm_num) (by norm_num)
    (by omega)
  have hstrict : digitSum k < 2 * (9 * m + 5) := by
    have : 9 * (2 * m + 1) + 2 - 1 = 2 * (9 * m + 5) := by omega
    rw [this] at hb he
    by_contra hge
    have := he (by omega)
    omega
  have hs : digitSum k = 9 * m + 5 := by
    obtain ⟨t, ht⟩ := hd
    have hpos := sum_pos hk
    have htpos : 0 < t := by nlinarith
    have htlt : t < 2 := by nlinarith
    have : t = 1 := by omega
    simpa [this] using ht
  have hk9 : k % 9 = 5 := by
    have hc := Nat.modEq_nine_digits_sum k
    change k % 9 = digitSum k % 9 at hc
    simpa [hs, Nat.add_mod, Nat.mul_mod] using hc
  have hsq9 : digitSum (k ^ 2) % 9 = 7 := by
    have hc := Nat.modEq_nine_digits_sum (k ^ 2)
    change (k ^ 2) % 9 = digitSum (k ^ 2) % 9 at hc
    rw [Nat.pow_mod, hk9] at hc
    norm_num at hc
    omega
  obtain ⟨t, ht⟩ := hd₂
  have ht9 : (5 * t) % 9 = 7 := by
    calc
      (5 * t) % 9 = ((9 * m + 5) * t) % 9 := by
        simp [Nat.mul_mod, Nat.add_mod]
      _ = 7 := by rw [← ht]; exact hsq9
  have ht5 : 5 ≤ t := by omega
  have hsq : k ^ 2 < 4 * 10 ^ (2 * (2 * m + 1)) := by
    rw [mul_comm 2 (2 * m + 1), pow_mul]
    have hp : 0 < 10 ^ (2 * m + 1) := by positivity
    have : k < 2 * 10 ^ (2 * m + 1) := by omega
    nlinarith
  have hbound := (sum_ceiling 4 (2 * (2 * m + 1)) (k ^ 2)
    (by norm_num) (by norm_num) hsq).1
  have hlower := Nat.mul_le_mul_left (9 * m + 5) ht5
  omega

/-- Chai Wah Wu's Oct 01 2025 conjecture for OEIS A389000. -/
theorem wu_conjecture (m : ℕ) : a (9 * m + 5) = 2 * 10 ^ (2 * m + 1) - 1 := by
  apply IsLeast.csInf_eq
  constructor
  · change 0 < 2 * 10 ^ (2 * m + 1) - 1 ∧ _
    have hp : 0 < 10 ^ (2 * m + 1) := by positivity
    refine ⟨by omega, ?_, ?_⟩
    · rw [digitSum_witness]
      exact dvd_mul_left _ _
    · rw [digitSum_witness_sq]
      exact dvd_mul_left _ _
  · intro k hk
    exact witness_minimal m k hk.1 hk.2.1 hk.2.2

#print axioms digitSum_witness
#print axioms digitSum_witness_sq
#print axioms wu_conjecture

end D5.S1.Digit.Admissibility.DigitSumSquareLeastWitness

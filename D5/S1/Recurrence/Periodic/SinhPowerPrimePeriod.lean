/- GID: D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/SinhPowerPrimePeriod
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.balaConjectureTwo; result=D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.bala_conjecture_two_false; claim=D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.balaConjectureTwo
   digest: A224899 has period p-1 modulo every odd prime; the p=2 assertion is false. -/

import D5.S1.Recurrence.Periodic.AlternatingWeightStirlingPrimePeriod

/-!
# The prime-period question for OEIS A224899

The finite exponential expansion of `n! [x^n] sinh(k*x)^k` defines `H n k`.
Summing it over `k ≤ n` defines `a n`. The analytic e.g.f. identity
`Sum_{k≥0} sinh(k*x)^k` is not formalized; the formal starting point is the
explicit finite coefficient formula. Integer division in that formula is
proved exact by `coefficient_bridge`, including at `k = 0`.

The binomial theorem and Stirling inclusion-exclusion expand the shifted
powers. Splitting at `r < k` exposes the factor `2^k * k!` in the numerator.
The bridge uses `r ∈ range (n+1)` instead of `k ≤ r ≤ n`: the additional
terms vanish by the Stirling diagonal bound. Thus `k!` divides `H n k`, and
`H n k = 0` for `n < k`. These are the two bounds needed for the fixed prime
window. At odd primes, division by `2^k` is invertible, giving an exponential
sum with coefficients independent of `n`. The imported positive-power
period theorem finishes the odd-prime case. The period need not be minimal.

The sign convention `(-1)^(k-j)` and base `k*(2*j-k)` come directly from
expanding `(exp(k*x)-exp(-k*x))^k`; replacing `j` by `k-j` gives the equivalent
convention `(-1)^j` and base `k*(k-2*j)`.

The certified instance refutes the named `balaConjectureTwo`, using only
indices one and two. Its utility basis is refutes, not a numerical regression.
Source: Library/Recurrence/bala2022a224899.md.

Freeze prerequisites:
* `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod`,
  statement_id `sha256:bb8d68f48a9563145d227c059d406a517b8d7b87ba1900ae3da2c64e6563a0f9`.
* Its transitive prerequisite `D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod`,
  statement_id `sha256:de3301b051609b0cfd4822db18707fa5d6b43e7a78e550dda3911b35c172da11`.
-/

open Finset
namespace D5.S1.Recurrence.Periodic.SinhPowerPrimePeriod

private theorem shifted_expansion (n k : ℕ) :
    (∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) * (Nat.choose k j : ℤ) *
      (2 * (j : ℤ) - k) ^ n) =
    ∑ r ∈ range (n + 1), (Nat.choose n r : ℤ) * (-(k : ℤ)) ^ (n - r) *
      2 ^ r * ((k.factorial : ℤ) * (Nat.stirlingSecond r k : ℤ)) := by
  calc
    _ = ∑ j ∈ range (k + 1), ∑ r ∈ range (n + 1),
        (Nat.choose n r : ℤ) * (-(k : ℤ)) ^ (n - r) * 2 ^ r *
          ((-1 : ℤ) ^ (k - j) * (Nat.choose k j : ℤ) * (j : ℤ) ^ r) := by
      apply sum_congr rfl
      intro j hj
      rw [sub_eq_add_neg, add_pow, mul_sum]
      apply sum_congr rfl
      intro r hr
      rw [mul_pow]
      ring
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro r hr
      rw [← mul_sum,
        ← D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion]

private theorem numerator_bridge (n k : ℕ) :
    (∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) * (Nat.choose k j : ℤ) *
      ((k : ℤ) * (2 * (j : ℤ) - k)) ^ n) =
    2 ^ k * ((k : ℤ) ^ n * (k.factorial : ℤ) *
      ∑ r ∈ range (n + 1), (Nat.choose n r : ℤ) * (-(k : ℤ)) ^ (n - r) *
        2 ^ (r - k) * (Nat.stirlingSecond r k : ℤ)) := by
  calc
    _ = (k : ℤ) ^ n * ∑ j ∈ range (k + 1),
        (-1 : ℤ) ^ (k - j) * (Nat.choose k j : ℤ) * (2 * (j : ℤ) - k) ^ n := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [mul_pow]
      ring
    _ = _ := by
      rw [shifted_expansion, mul_sum, mul_sum, mul_sum]
      apply sum_congr rfl
      intro r hr
      by_cases hkr : k ≤ r
      · have ht : (2 : ℤ) ^ r = 2 ^ k * 2 ^ (r - k) := by
          rw [← pow_add, Nat.add_sub_of_le hkr]
        rw [ht]
        ring
      · simp [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_of_not_ge hkr)]

/-- The finite exponential expansion of n! [x^n] sinh(k*x)^k.
The exponential-generating-function identity itself is not formalized. -/
def H (n k : ℕ) : ℤ :=
  (∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) * (Nat.choose k j : ℤ) *
    ((k : ℤ) * (2 * (j : ℤ) - k)) ^ n) / 2 ^ k

/-- The factorial-bearing Stirling coefficient bridge. Terms r < k vanish. -/
theorem coefficient_bridge (n k : ℕ) :
    H n k = (k : ℤ) ^ n * (k.factorial : ℤ) *
      ∑ r ∈ range (n + 1), (Nat.choose n r : ℤ) * (-(k : ℤ)) ^ (n - r) *
        2 ^ (r - k) * (Nat.stirlingSecond r k : ℤ) := by
  rw [H, numerator_bridge]
  exact Int.mul_ediv_cancel_left _ (by positivity)

/-- A224899 from its finite exponential coefficient expansion. The e.g.f.
identity Sum_k sinh(k*x)^k is not itself formalized. -/
def a (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), H n k

private theorem H_eq_zero (n k : ℕ) (hnk : n < k) : H n k = 0 := by
  rw [coefficient_bridge]
  have hs : (∑ r ∈ range (n + 1), (Nat.choose n r : ℤ) * (-(k : ℤ)) ^ (n - r) *
      2 ^ (r - k) * (Nat.stirlingSecond r k : ℤ)) = 0 := by
    apply sum_eq_zero
    intro r hr
    have hrk : r < k := by have := mem_range.mp hr; omega
    simp [Nat.stirlingSecond_eq_zero_of_lt hrk]
  rw [hs, mul_zero]

/-- A fixed prime-sized window, including at index zero. -/
theorem a_window (p n : ℕ) (hp : p.Prime) :
    (a n : ZMod p) = ∑ k ∈ range p, (H n k : ZMod p) := by
  simp only [a, Int.cast_sum]
  rcases le_total (n + 1) p with h | h
  · apply sum_subset (range_mono h)
    intro k _ hk
    have hnk : n < k := by simp only [mem_range] at hk; omega
    simp [H_eq_zero n k hnk]
  · symm
    apply sum_subset (range_mono h)
    intro k _ hk
    have hpk : p ≤ k := by simpa only [mem_range, not_lt] using hk
    have hf : (k.factorial : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_factorial hp.pos hpk)
    simp only [coefficient_bridge, Int.cast_mul, Int.cast_natCast, hf, mul_zero, zero_mul]

/-- The coefficients and summation window are independent of n. -/
theorem a_exponential_sum (p n : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    (a n : ZMod p) = ∑ k ∈ range p, ∑ j ∈ range (k + 1),
      (2 : ZMod p)⁻¹ ^ k * ((-1 : ZMod p) ^ (k - j) * (Nat.choose k j : ZMod p)) *
        ((k : ZMod p) * (2 * (j : ZMod p) - k)) ^ n := by
  let : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    exact hodd ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one)
  rw [a_window p n hp]
  apply sum_congr rfl
  intro k hk
  unfold H
  rw [Int.cast_div (by rw [numerator_bridge]; exact dvd_mul_right _ _)
    (by simpa using pow_ne_zero k htwo)]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, Int.cast_sub, Int.cast_ofNat, div_eq_mul_inv, ← inv_pow, sum_mul]
  apply sum_congr rfl
  intro j hj
  ring

/-- Bala's period p-1 assertion for every odd prime and every positive index.
The period is not asserted to be minimal. -/
theorem bala_conjecture_odd (p n : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hn : 1 ≤ n) :
    (a (n + (p - 1)) : ZMod p) = (a n : ZMod p) := by
  rw [a_exponential_sum p _ hp hodd, a_exponential_sum p _ hp hodd]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro j hj
  rw [D5.S1.Recurrence.Periodic.AlternatingWeightStirlingPrimePeriod.pow_add_pred_prime hp _ n hn]

/-- The p=2 instance of Bala's conjecture: period one from index one. -/
def balaConjectureTwo : Prop :=
  ∀ n : ℕ, 1 ≤ n → (a (n + 1) : ZMod 2) = (a n : ZMod 2)

/-- The claimed period one fails since a(1)=1 and a(2)=8.
utility: kind=certified-instance; basis=refutes
The named claim is balaConjectureTwo. -/
theorem bala_conjecture_two_false : ¬ balaConjectureTwo := by
  intro h
  have h1 := h 1 (by omega)
  norm_num [a, H, sum_range_succ] at h1
  exact (by decide : (8 : ZMod 2) ≠ 1) h1

#print axioms H
#print axioms coefficient_bridge
#print axioms a
#print axioms a_window
#print axioms a_exponential_sum
#print axioms bala_conjecture_odd
#print axioms balaConjectureTwo
#print axioms bala_conjecture_two_false

end D5.S1.Recurrence.Periodic.SinhPowerPrimePeriod

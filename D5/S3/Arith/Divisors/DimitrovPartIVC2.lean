/- GID: D5/S3/Arith/Divisors/DimitrovPartIVC2
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/DimitrovPartIVC2
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The full second conjecture of Dimitrov and Lazarova Part 4 follows from an ordered ratio inequality. -/

import D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5

set_option autoImplicit false

namespace D5.S3.Arith.Divisors.DimitrovPartIVC2

open D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes (psi)
open D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5 (psi_ge sigma_ge_psi)

/-- Conjecture 2 of Part 4, with all powers of the actual arithmetic-function values. -/
def claim : Prop := ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k →
  ((Nat.totient n : ℝ) ^ (3 * k) * (psi n : ℝ) ^ (3 * k) +
    (psi n : ℝ) ^ (3 * k) * (ArithmeticFunction.sigma 1 n : ℝ) ^ (3 * k) +
    (Nat.totient n : ℝ) ^ (3 * k) * (ArithmeticFunction.sigma 1 n : ℝ) ^ (3 * k)) /
    ((Nat.totient n : ℝ) ^ (2 * k) * (psi n : ℝ) ^ (2 * k) *
      (ArithmeticFunction.sigma 1 n : ℝ) ^ (2 * k)) ≥
  (2 * ((n : ℝ) ^ 2 - 1) ^ (3 * k) + ((n : ℝ) + 1) ^ (6 * k)) /
    (((n : ℝ) - 1) ^ (2 * k) * ((n : ℝ) + 1) ^ (4 * k))

private lemma ordered_ratio_bound {r x y : ℝ}
    (hr : 1 ≤ r) (hrx : r ≤ x) (hxy : x ≤ y) :
    r ^ 2 + 2 / r ≤ x * y + x / y ^ 2 + y / x ^ 2 := by
  have hx1 : 1 ≤ x := hr.trans hrx
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hy : 0 < y := hx.trans_le hxy
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hx3 : 0 ≤ x ^ 3 - 1 := sub_nonneg.mpr (one_le_pow₀ hx1)
  have hdiff : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hfirst : 0 ≤ x * y + x / y ^ 2 + y / x ^ 2 - (x ^ 2 + 2 / x) := by
    have hid : x * y + x / y ^ 2 + y / x ^ 2 - (x ^ 2 + 2 / x) =
        (y - x) * ((x ^ 3 - 1) * y ^ 2 + (y - x) * (2 * y + x)) /
          (x ^ 2 * y ^ 2) := by
      field_simp [hx.ne', hy.ne', hr0.ne']
      <;> ring
    rw [hid]
    exact div_nonneg
      (mul_nonneg hdiff (add_nonneg (mul_nonneg hx3 (sq_nonneg y))
        (mul_nonneg hdiff (by positivity)))) (by positivity)
  have hxr : 1 ≤ x * r := one_le_mul_of_one_le_of_one_le hx1 hr
  have hbracket : 0 ≤ (x + r) * x * r - 2 := by
    have hm := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ x + r by linarith)
      (show 0 ≤ x * r by positivity)
    nlinarith
  have hsecond : 0 ≤ x ^ 2 + 2 / x - (r ^ 2 + 2 / r) := by
    have hid : x ^ 2 + 2 / x - (r ^ 2 + 2 / r) =
        (x - r) * ((x + r) * x * r - 2) / (x * r) := by
      field_simp [hx.ne', hy.ne', hr0.ne']
      <;> ring
    rw [hid]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hrx) hbracket) (by positivity)
  linarith

/-- The complete original Part 4 Conjecture 2 for every natural n ≥ 2 and k ≥ 1. -/
theorem result : claim := by
  intro n hn k _hk
  have hn0 : 0 < n := by omega
  have ha : 0 < (Nat.totient n : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hn0)
  have hau : (Nat.totient n : ℝ) ≤ (n : ℝ) - 1 := by
    have ht : Nat.totient n + 1 ≤ n := Nat.succ_le_of_lt (Nat.totient_lt n (by omega))
    have ht' : (Nat.totient n : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast ht
    linarith
  have hvb : (n : ℝ) + 1 ≤ (psi n : ℝ) := by exact_mod_cast psi_ge hn
  have hbc : (psi n : ℝ) ≤ (ArithmeticFunction.sigma 1 n : ℝ) := by
    exact_mod_cast sigma_ge_psi hn
  have hu : 0 < (n : ℝ) - 1 := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hv : 0 < (n : ℝ) + 1 := by positivity
  have hb : 0 < (psi n : ℝ) := hv.trans_le hvb
  have hc : 0 < (ArithmeticFunction.sigma 1 n : ℝ) := hb.trans_le hbc
  let A : ℝ := (Nat.totient n : ℝ) ^ k
  let B : ℝ := (psi n : ℝ) ^ k
  let C : ℝ := (ArithmeticFunction.sigma 1 n : ℝ) ^ k
  let U : ℝ := ((n : ℝ) - 1) ^ k
  let V : ℝ := ((n : ℝ) + 1) ^ k
  have hA : 0 < A := pow_pos ha k
  have hB : 0 < B := pow_pos hb k
  have hC : 0 < C := pow_pos hc k
  have hU : 0 < U := pow_pos hu k
  have hV : 0 < V := pow_pos hv k
  have hr : 1 ≤ V / U := by
    rw [← div_pow]
    exact one_le_pow₀ ((one_le_div hu).mpr (by linarith))
  have hrx : V / U ≤ B / A := by
    change ((n : ℝ) + 1) ^ k / ((n : ℝ) - 1) ^ k ≤
      (psi n : ℝ) ^ k / (Nat.totient n : ℝ) ^ k
    rw [← div_pow, ← div_pow]
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div₀ (by positivity) hvb ha hau
  have hxy : B / A ≤ C / A :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hb.le hbc k) hA.le
  have hbound := ordered_ratio_bound hr hrx hxy
  have hlhs :
      (A ^ 3 * B ^ 3 + B ^ 3 * C ^ 3 + A ^ 3 * C ^ 3) /
        (A ^ 2 * B ^ 2 * C ^ 2) = B / A * (C / A) + (B / A) / (C / A) ^ 2 +
          (C / A) / (B / A) ^ 2 := by
    field_simp [hA.ne', hB.ne', hC.ne', hU.ne', hV.ne']
    <;> ring
  have hrhs : (2 * (U * V) ^ 3 + V ^ 6) / (U ^ 2 * V ^ 4) =
      (V / U) ^ 2 + 2 / (V / U) := by
    field_simp [hA.ne', hB.ne', hC.ne', hU.ne', hV.ne']
    <;> ring
  have hnormalized :
      (2 * (U * V) ^ 3 + V ^ 6) / (U ^ 2 * V ^ 4) ≤
      (A ^ 3 * B ^ 3 + B ^ 3 * C ^ 3 + A ^ 3 * C ^ 3) /
        (A ^ 2 * B ^ 2 * C ^ 2) := by
    rw [hlhs, hrhs]
    exact hbound
  dsimp [A, B, C, U, V] at hnormalized
  rw [show (n : ℝ) ^ 2 - 1 = ((n : ℝ) - 1) * ((n : ℝ) + 1) by ring]
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm] using hnormalized

#print axioms ordered_ratio_bound
#print axioms result

end D5.S3.Arith.Divisors.DimitrovPartIVC2

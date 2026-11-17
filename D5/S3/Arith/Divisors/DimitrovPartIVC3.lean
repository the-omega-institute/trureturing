/- GID: D5/S3/Arith/Divisors/DimitrovPartIVC3
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/DimitrovPartIVC3
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A candidate proof of the complete Part IV third conjecture. -/

import D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5

/-! The whole pair-sum powers are compared through a geometric-mean envelope. -/

set_option autoImplicit false
namespace D5.S3.Arith.Divisors.DimitrovPartIVC3
open D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes

def claim : Prop := ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k →
  (((Nat.totient n : ℝ) + psi n) ^ (3 * k) +
    ((psi n : ℝ) + ArithmeticFunction.sigma 1 n) ^ (3 * k) +
    ((Nat.totient n : ℝ) + ArithmeticFunction.sigma 1 n) ^ (3 * k)) /
    (((Nat.totient n : ℝ) + psi n) ^ k *
      ((psi n : ℝ) + ArithmeticFunction.sigma 1 n) ^ k *
      ((Nat.totient n : ℝ) + ArithmeticFunction.sigma 1 n) ^ k) ≥
  (2 * (n : ℝ) ^ (3 * k) + ((n : ℝ) + 1) ^ (3 * k)) /
    ((n : ℝ) ^ (2 * k) * ((n : ℝ) + 1) ^ k)

private lemma cubic_envelope {x y z q : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hq : 1 ≤ q)
    (hgap : q ^ 2 * x * y ≤ z ^ 2) :
    q ^ 2 + 2 / q ≤ (x ^ 3 + y ^ 3 + z ^ 3) / (x * y * z) := by
  let u := Real.sqrt (x * y)
  have hu : 0 < u := Real.sqrt_pos.2 (mul_pos hx hy)
  have hu2 : u ^ 2 = x * y := Real.sq_sqrt (mul_pos hx hy).le
  have hsum : 2 * u ≤ x + y := by
    nlinarith [sq_nonneg (x - y)]
  have hcubes : 2 * u ^ 3 ≤ x ^ 3 + y ^ 3 := by
    have hp := mul_nonneg (sub_nonneg.mpr hsum) (sq_nonneg (x + y + u))
    nlinarith [hu2, mul_nonneg (sq_nonneg (x + y + u)) (sub_nonneg.mpr hsum)]
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqu : q * u ≤ z := by nlinarith [hgap]
  have ht : q ≤ z / u := (le_div_iff₀ hu).2 hqu
  have hmono : q ^ 2 + 2 / q ≤ (z / u) ^ 2 + 2 / (z / u) := by
    have ht1 : 1 ≤ z / u := hq.trans ht
    have hp : 0 ≤ (z / u - q) * (q * (z / u) * (z / u + q) - 2) := by
      apply mul_nonneg (sub_nonneg.mpr ht)
      nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr ht1)]
    apply (le_of_sub_nonneg ?_)
    have heq : ((z / u) ^ 2 + 2 / (z / u) - (q ^ 2 + 2 / q)) *
        (q * (z / u)) = (z / u - q) * (q * (z / u) * (z / u + q) - 2) := by
      field_simp
      <;> ring
    nlinarith [mul_pos hq0 (div_pos hz hu)]
  have hlast : (z / u) ^ 2 + 2 / (z / u) ≤
      (x ^ 3 + y ^ 3 + z ^ 3) / (x * y * z) := by
    apply (le_div_iff₀ (mul_pos (mul_pos hx hy) hz)).2
    have heq : ((z / u) ^ 2 + 2 / (z / u)) * (x * y * z) =
        2 * u ^ 3 + z ^ 3 := by
      rw [← hu2]
      field_simp
      <;> ring
    rw [heq]
    linarith
  exact hmono.trans hlast

private lemma pair_gap {a b c q : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (hq : 1 ≤ q)
    (hqa : q * (a + b) ≤ 2 * b) :
    q ^ 2 * (a + b) * (a + c) ≤ (b + c) ^ 2 := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hsq : q ^ 2 * (a + b) ^ 2 ≤ 4 * b ^ 2 := by
    have hp := pow_le_pow_left₀ (show 0 ≤ q * (a + b) by positivity) hqa 2
    nlinarith only [hp]
  have hprod : 4 * b ^ 2 * (a + c) ≤ (a + b) * (b + c) ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hbc)
      (show 0 ≤ (a + b) * (c - b) + 4 * a * b by positivity)
    nlinarith [hp]
  have hmul := mul_le_mul_of_nonneg_right hsq (show 0 ≤ a + c by positivity)
  have habpos : 0 < a + b := by positivity
  nlinarith [hprod, hmul]

theorem result : claim := by
  intro n hn k hk
  let a : ℝ := Nat.totient n
  let b : ℝ := psi n
  let c : ℝ := ArithmeticFunction.sigma 1 n
  let q : ℝ := ((n : ℝ) + 1) / n
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast (Nat.totient_pos.mpr (show 0 < n by omega))
  have han : a ≤ (n : ℝ) - 1 := by
    have h := Nat.succ_le_of_lt (Nat.totient_lt n (by omega))
    have h' : a + 1 ≤ (n : ℝ) := by dsimp [a]; exact_mod_cast h
    linarith
  have hbn : (n : ℝ) + 1 ≤ b := by
    dsimp [b]
    exact_mod_cast DimitrovLowerBoundsC4C5.psi_ge hn
  have hbc : b ≤ c := by
    dsimp [b, c]
    exact_mod_cast DimitrovLowerBoundsC4C5.sigma_ge_psi hn
  have hb : 0 < b := by linarith
  have hc : 0 < c := hb.trans_le hbc
  have hq : 1 ≤ q := by dsimp [q]; apply (le_div_iff₀ hn0).2; linarith
  have hqa : q * (a + b) ≤ 2 * b := by
    dsimp [q]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hn0).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hbn) (show 0 ≤ (n : ℝ) - 1 by linarith),
      mul_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) (sub_nonneg.mpr han)]
  have hg := pair_gap ha (by linarith) hbc hq hqa
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ q ^ 2 * (a + b) * (a + c)) hg k
  have hgap : (q ^ k) ^ 2 * (a + b) ^ k * (a + c) ^ k ≤ ((b + c) ^ k) ^ 2 := by
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm k 2] using hpow
  have hqk : 1 ≤ q ^ k := one_le_pow₀ hq
  have h := cubic_envelope (pow_pos (add_pos ha hb) k)
    (pow_pos (add_pos ha hc) k) (pow_pos (add_pos hb hc) k) hqk hgap
  have hrhs : (q ^ k) ^ 2 + 2 / q ^ k =
      (2 * (n : ℝ) ^ (3 * k) + ((n : ℝ) + 1) ^ (3 * k)) /
        ((n : ℝ) ^ (2 * k) * ((n : ℝ) + 1) ^ k) := by
    dsimp [q]
    simp only [Nat.mul_comm 3 k, Nat.mul_comm 2 k, pow_mul, div_pow]
    field_simp [hn0.ne', (show (n : ℝ) + 1 ≠ 0 by positivity)]
    <;> ring
  rw [hrhs] at h
  change ((a + b) ^ (3 * k) + (b + c) ^ (3 * k) + (a + c) ^ (3 * k)) /
      ((a + b) ^ k * (b + c) ^ k * (a + c) ^ k) ≥ _
  convert h using 1 <;> simp only [pow_mul, mul_comm 3 k] <;> ring

#print axioms result
end D5.S3.Arith.Divisors.DimitrovPartIVC3

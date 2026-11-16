/- GID: D5/S3/Arith/Divisors/DimitrovPartFourC4
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/DimitrovPartFourC4
   mirror-E: none(waiver:probe)
   anchors: []
   utility: none
   digest: Complete Part IV Conjecture 4 via ordered mixed ratios. -/
/-
Source: Stoyan Dimitrov and Meglena Lazarova, Mathematics 14(21), 3935,
DOI 10.3390/math14213935, Section 4, Conjecture 4, PDF page 13,
XML mm202--mm204; definitions Section 1. Source license: CC BY 4.0.
The full source inequality uses ordinary powers and real subtraction.
proof_shape: cubic_ratio_bound is bind-only polynomial normalization of
nonnegative products and squares; its live consumer is result.
proof_shape: result is bind-only after inlining the consumed auxiliary.
Admission candidate: external open-problem-resolution, issue #30640.
No escape witness, freezing, registration or publication is asserted.
-/
import D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5

/-! A mixed-ratio proof of the full power quotient in Part IV Conjecture 4. -/
set_option autoImplicit false
namespace D5.S3.Arith.Divisors.DimitrovPartFourC4
open D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes
open D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5

/-- Cubic quotient bound on a positive ratio quadrant; consumed by `result`. -/
private lemma cubic_ratio_bound {x y r : ℝ}
    (hr : 1 ≤ r) (hx : r ≤ x) (hy : r ≤ y) :
    (1 + 2 * r ^ 3) / r ^ 2 ≤ (1 + x ^ 3 + y ^ 3) / (x * y) := by
  have hr0 : 0 < r := by linarith
  have hx0 : 0 < x := hr0.trans_le hx
  have hy0 : 0 < y := hr0.trans_le hy
  have hu : 0 ≤ x - r := sub_nonneg.mpr hx
  have hv : 0 ≤ y - r := sub_nonneg.mpr hy
  have hr3 : 1 ≤ r ^ 3 := one_le_pow₀ hr
  have hc : 0 ≤ r ^ 3 - 1 := by linarith
  have hd : 0 ≤ 4 * r ^ 3 - 1 := by linarith
  have hid : r ^ 2 * (1 + x ^ 3 + y ^ 3) - (1 + 2 * r ^ 3) * x * y =
      r * (r ^ 3 - 1) * ((x - r) + (y - r)) +
      3 * r ^ 3 * ((x - r) - (y - r)) ^ 2 +
      (4 * r ^ 3 - 1) * (x - r) * (y - r) +
      r ^ 2 * ((x - r) ^ 3 + (y - r) ^ 3) := by ring
  apply (div_le_div_iff₀ (sq_pos_of_pos hr0) (mul_pos hx0 hy0)).2
  have hp : 0 ≤ r ^ 2 * (1 + x ^ 3 + y ^ 3) - (1 + 2 * r ^ 3) * x * y := by
    rw [hid]
    positivity
  nlinarith only [hp]

/-- The complete original source statement, with ordinary real arithmetic. -/
def claim : Prop := ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k →
  ((Nat.totient n : ℝ) ^ (3 * k) * ((psi n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ)) ^ (3 * k) +
    (psi n : ℝ) ^ (3 * k) * ((Nat.totient n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ)) ^ (3 * k) +
    (ArithmeticFunction.sigma 1 n : ℝ) ^ (3 * k) * ((Nat.totient n : ℝ) + (psi n : ℝ)) ^ (3 * k)) /
    ((Nat.totient n : ℝ) ^ k * (psi n : ℝ) ^ k * (ArithmeticFunction.sigma 1 n : ℝ) ^ k *
      ((Nat.totient n : ℝ) + (psi n : ℝ)) ^ k *
      ((psi n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ)) ^ k *
      ((Nat.totient n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ)) ^ k) ≥
    (2 * (n : ℝ) ^ (3 * k) + ((n : ℝ) - 1) ^ (3 * k)) /
      ((n : ℝ) ^ (2 * k) * ((n : ℝ) - 1) ^ k)

/-- Full Part IV C4, without a restriction on the positive integer exponent. -/
theorem result : claim := by
  intro n hn k _hk
  have hn0 : 0 < n := by omega
  have ha0 : 0 < (Nat.totient n : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr hn0)
  have ha_le_nat : Nat.totient n + 1 ≤ n := Nat.succ_le_of_lt (Nat.totient_lt n (by omega))
  have ha_le : (Nat.totient n : ℝ) ≤ (n : ℝ) - 1 := by
    have h : (Nat.totient n : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast ha_le_nat
    linarith
  have hb_lower : (n : ℝ) + 1 ≤ (psi n : ℝ) := by exact_mod_cast psi_ge hn
  have hbc : (psi n : ℝ) ≤ (ArithmeticFunction.sigma 1 n : ℝ) := by
    exact_mod_cast sigma_ge_psi hn
  have hb0 : 0 < (psi n : ℝ) := lt_of_lt_of_le (by positivity) hb_lower
  have hc0 : 0 < (ArithmeticFunction.sigma 1 n : ℝ) := hb0.trans_le hbc
  have hnminus : 0 < (n : ℝ) - 1 := by
    have h : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    linarith
  let q : ℝ := ((n : ℝ) + 1) / ((n : ℝ) - 1)
  let r : ℝ := (n : ℝ) / ((n : ℝ) - 1)
  have hq : 1 ≤ q := by dsimp [q]; apply (le_div_iff₀ hnminus).2; linarith
  have hqr : q ≤ (psi n : ℝ) / (Nat.totient n : ℝ) := by
    dsimp [q]
    apply (div_le_div_iff₀ hnminus ha0).2
    nlinarith
  have hr : 1 ≤ r := by dsimp [r]; apply (le_div_iff₀ hnminus).2; linarith
  let A : ℝ := (Nat.totient n : ℝ) * ((psi n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ))
  let B : ℝ := (psi n : ℝ) * ((Nat.totient n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ))
  let C : ℝ := (ArithmeticFunction.sigma 1 n : ℝ) * ((Nat.totient n : ℝ) + (psi n : ℝ))
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hm := mixed_bound (a := (Nat.totient n : ℝ)) (b := (psi n : ℝ))
    (c := (ArithmeticFunction.sigma 1 n : ℝ)) (q := q) (m := 1)
    ha0 (by linarith) hbc (by omega) hq hqr
  have heq : q ^ (1 - 1) * (1 + q) / 2 = r := by
    dsimp [q, r]
    norm_num
    field_simp [hnminus.ne']
    <;> ring
  have hBA : r ≤ B / A := by simpa only [heq, pow_one] using hm.2.2
  have hBC : B ≤ C := by simpa only [pow_one] using hm.2.1
  have hCA : r ≤ C / A := hBA.trans (div_le_div_of_nonneg_right hBC hA.le)
  have hmain := cubic_ratio_bound (one_le_pow₀ hr : 1 ≤ r ^ k)
    (pow_le_pow_left₀ (by linarith : 0 ≤ r) hBA k)
    (pow_le_pow_left₀ (by linarith : 0 ≤ r) hCA k)
  have hnorm :
      (1 + ((B / A) ^ k) ^ 3 + ((C / A) ^ k) ^ 3) /
        ((B / A) ^ k * (C / A) ^ k) =
      ((A ^ k) ^ 3 + (B ^ k) ^ 3 + (C ^ k) ^ 3) / (A ^ k * B ^ k * C ^ k) := by
    simp only [div_pow]
    field_simp [hA.ne', hB.ne', hC.ne']
    <;> ring
  rw [hnorm] at hmain
  have hnreal : (n : ℝ) ≠ 0 := by positivity
  have hrhs : (1 + 2 * (r ^ k) ^ 3) / (r ^ k) ^ 2 =
      (2 * (n : ℝ) ^ (3 * k) + ((n : ℝ) - 1) ^ (3 * k)) /
        ((n : ℝ) ^ (2 * k) * ((n : ℝ) - 1) ^ k) := by
    dsimp [r]
    simp only [div_pow, pow_mul, mul_comm 3 k, mul_comm 2 k]
    field_simp [hnreal, hnminus.ne']
    <;> ring
  rw [hrhs] at hmain
  convert hmain using 1 <;>
    dsimp [A, B, C] <;>
    simp only [mul_pow, pow_mul, mul_comm 3 k] <;> ring

#print axioms result
end D5.S3.Arith.Divisors.DimitrovPartFourC4

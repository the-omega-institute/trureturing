/- GID: D5/S3/Arith/Divisors/DimitrovPartFourC1
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/DimitrovPartFourC1
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Complete Part IV Conjecture 1 by the cubic ratio bound. -/

/-
Source. Stoyan Dimitrov and Meglena Lazarova, Mathematics 14(21), 3935,
DOI 10.3390/math14213935, Section 4, Conjecture 1, PDF page 13.
The arithmetic functions are defined in Section 1. Source license CC BY 4.0.
The claim definition is consumed by result. The result is bind-only by
direct application and field normalization. Intended admission basis
open-problem-resolution, issue #35004, records the exact statement and
bounded literature search.
-/
import D5.S3.Arith.Divisors.DimitrovPartFourC4

/-! The full positive-power quotient in Part IV Conjecture 1. -/

set_option autoImplicit false

namespace D5.S3.Arith.Divisors.DimitrovPartFourC1

open D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes (psi)
open D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5 (psi_ge sigma_ge_psi)
open D5.S3.Arith.Divisors.DimitrovPartFourC4 (cubic_ratio_bound)

/-- The complete original conjecture with real subtraction and division. -/
def claim : Prop := ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k →
  ((Nat.totient n : ℝ) ^ (3 * k) + (psi n : ℝ) ^ (3 * k) +
      (ArithmeticFunction.sigma 1 n : ℝ) ^ (3 * k)) /
    ((Nat.totient n : ℝ) ^ k * (psi n : ℝ) ^ k *
      (ArithmeticFunction.sigma 1 n : ℝ) ^ k) ≥
  (2 * ((n : ℝ) + 1) ^ (3 * k) + ((n : ℝ) - 1) ^ (3 * k)) /
    (((n : ℝ) + 1) ^ (2 * k) * ((n : ℝ) - 1) ^ k)

/-- The source inequality for all natural `n ≥ 2` and `k ≥ 1`. -/
theorem result : claim := by
  intro n hn k _hk
  have hn0 : 0 < n := by omega
  have ha : 0 < (Nat.totient n : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn0
  have hau : (Nat.totient n : ℝ) ≤ (n : ℝ) - 1 := by
    have h := Nat.totient_lt n (by omega)
    have h' : (Nat.totient n : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt h
    linarith
  have hvb : (n : ℝ) + 1 ≤ (psi n : ℝ) := by exact_mod_cast psi_ge hn
  have hbc : (psi n : ℝ) ≤ (ArithmeticFunction.sigma 1 n : ℝ) := by
    exact_mod_cast sigma_ge_psi hn
  have hu : 0 < (n : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hv : 0 < (n : ℝ) + 1 := by positivity
  have hb : 0 < (psi n : ℝ) := hv.trans_le hvb
  have hc : 0 < (ArithmeticFunction.sigma 1 n : ℝ) := hb.trans_le hbc
  let A := (Nat.totient n : ℝ) ^ k
  let B := (psi n : ℝ) ^ k
  let C := (ArithmeticFunction.sigma 1 n : ℝ) ^ k
  let U := ((n : ℝ) - 1) ^ k
  let V := ((n : ℝ) + 1) ^ k
  have hA : 0 < A := pow_pos ha k
  have hU : 0 < U := pow_pos hu k
  have hV : 0 < V := pow_pos hv k
  have hB : 0 < B := pow_pos hb k
  have hC : 0 < C := pow_pos hc k
  have hAU : A ≤ U := pow_le_pow_left₀ ha.le hau k
  have hVB : V ≤ B := pow_le_pow_left₀ hv.le hvb k
  have hVC : V ≤ C := pow_le_pow_left₀ hv.le (hvb.trans hbc) k
  have hUV : U ≤ V := pow_le_pow_left₀ hu.le (by linarith) k
  have hr : 1 ≤ V / U := (one_le_div hU).2 hUV
  have hx : V / U ≤ B / A := (div_le_div_iff₀ hU hA).2
    ((mul_le_mul_of_nonneg_right hVB hA.le).trans
      (mul_le_mul_of_nonneg_left hAU hB.le))
  have hy : V / U ≤ C / A := (div_le_div_iff₀ hU hA).2
    ((mul_le_mul_of_nonneg_right hVC hA.le).trans
      (mul_le_mul_of_nonneg_left hAU hC.le))
  have h := cubic_ratio_bound hr hx hy
  have heqL : (1 + 2 * (V / U) ^ 3) / (V / U) ^ 2 =
      (2 * V ^ 3 + U ^ 3) / (V ^ 2 * U) := by
    field_simp [hU.ne', hV.ne']
    <;> ring
  have heqR : (1 + (B / A) ^ 3 + (C / A) ^ 3) / (B / A * (C / A)) =
      (A ^ 3 + B ^ 3 + C ^ 3) / (A * B * C) := by
    field_simp [hA.ne', hB.ne', hC.ne']
    <;> ring
  rw [heqL, heqR] at h
  simpa only [A, B, C, U, V, ← pow_mul, Nat.mul_comm k 3, Nat.mul_comm k 2] using h

#print axioms result

end D5.S3.Arith.Divisors.DimitrovPartFourC1

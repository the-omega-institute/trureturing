/- GID: D5/S3/Arith/Divisors/DimitrovPartIVC1
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/DimitrovPartIVC1
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Complete Part IV Conjecture 1 via the cubic ratio bound. -/
import D5.S3.Arith.Divisors.DimitrovPartFourC4

/-! The full power-family quotient in Dimitrov and Lazarova Part IV, Conjecture 1. -/

set_option autoImplicit false

namespace D5.S3.Arith.Divisors.DimitrovPartIVC1

open OeisA344695GcdSigmaPsiPrimes (psi)
open DimitrovLowerBoundsC4C5 (psi_ge sigma_ge_psi)

/-- The publisher's inequality for all natural `n ≥ 2` and `k ≥ 1`. -/
def claim : Prop := ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k →
    ((Nat.totient n : ℝ) ^ (3 * k) + (psi n : ℝ) ^ (3 * k) +
      (ArithmeticFunction.sigma 1 n : ℝ) ^ (3 * k)) /
      ((Nat.totient n : ℝ) ^ k * (psi n : ℝ) ^ k *
        (ArithmeticFunction.sigma 1 n : ℝ) ^ k) ≥
    (2 * ((n : ℝ) + 1) ^ (3 * k) + ((n : ℝ) - 1) ^ (3 * k)) /
      (((n : ℝ) + 1) ^ (2 * k) * ((n : ℝ) - 1) ^ k)

/-- The complete first conjecture follows by normalizing both cubic quotients. -/
theorem result : claim := by
  intro n hn k _hk
  have ha : 0 < (Nat.totient n : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (show 0 < n by omega))
  have hau : (Nat.totient n : ℝ) ≤ (n : ℝ) - 1 := by
    have h : Nat.totient n + 1 ≤ n := Nat.succ_le_of_lt (Nat.totient_lt n (by omega))
    have hreal : (Nat.totient n : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h
    linarith
  have hvb : (n : ℝ) + 1 ≤ (psi n : ℝ) := by exact_mod_cast psi_ge hn
  have hbc : (psi n : ℝ) ≤ (ArithmeticFunction.sigma 1 n : ℝ) := by
    exact_mod_cast sigma_ge_psi hn
  have hu : 0 < (n : ℝ) - 1 := by
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
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
    dsimp [U, V]
    rw [← div_pow]
    exact one_le_pow₀ ((one_le_div hu).mpr (by linarith))
  have hrx : V / U ≤ B / A := by
    dsimp [A, B, U, V]
    rw [← div_pow, ← div_pow]
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div₀ hb.le hvb ha hau
  have hxy : B / A ≤ C / A :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hb.le hbc k) hA.le
  have hbound := DimitrovPartFourC4.cubic_ratio_bound hr hrx (hrx.trans hxy)
  have hnormalized :
      (2 * V ^ 3 + U ^ 3) / (V ^ 2 * U) ≤
        (A ^ 3 + B ^ 3 + C ^ 3) / (A * B * C) := by
    calc
      _ = (1 + 2 * (V / U) ^ 3) / (V / U) ^ 2 := by
        field_simp [hU.ne', hV.ne'] <;> ring
      _ ≤ (1 + (B / A) ^ 3 + (C / A) ^ 3) / ((B / A) * (C / A)) := hbound
      _ = _ := by
        field_simp [hA.ne', hB.ne', hC.ne'] <;> ring
  simpa only [A, B, C, U, V, ← pow_mul, Nat.mul_comm k 3, Nat.mul_comm k 2] using hnormalized

end D5.S3.Arith.Divisors.DimitrovPartIVC1

/- GID: D5/S3/Arith/Divisors/DimitrovLowerBoundC6
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/DimitrovLowerBoundC6
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Dimitrov's Conjecture 6 follows from the full Conjecture 5 reciprocal-product bound. -/

/-
admission_basis: open-problem-resolution (#30478; candidate Proved)
escape_witness: none
proof_shape:
  claim: bind-only source definition; consumer: result.
  result: bind-only; external endpoint: arXiv:2606.12484v1, Conjecture 6.
Direct frozen dependency: D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.result5.
The only mathematical steps beyond that dependency are positivity and exact field normalization.
The full natural-number ranges n ≥ 2 and k ≥ 1 and all pointwise powers are retained.
-/

import D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5

/-! The complete sixth source conjecture is obtained by exact normalization of the fifth. -/

set_option autoImplicit false

namespace D5.S3.Arith.Divisors.DimitrovLowerBoundC6

open D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes

/-- Dimitrov's complete original Conjecture 6, with powers of function values. -/
def claim : Prop := ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k →
  ((Nat.totient n : ℝ) ^ k * (psi n : ℝ) ^ k /
      ((ArithmeticFunction.sigma 1 n : ℝ) ^ k *
        ((Nat.totient n : ℝ) ^ k + (psi n : ℝ) ^ k)) +
    (Nat.totient n : ℝ) ^ k * (ArithmeticFunction.sigma 1 n : ℝ) ^ k /
      ((psi n : ℝ) ^ k *
        ((Nat.totient n : ℝ) ^ k + (ArithmeticFunction.sigma 1 n : ℝ) ^ k)) +
    (psi n : ℝ) ^ k * (ArithmeticFunction.sigma 1 n : ℝ) ^ k /
      ((Nat.totient n : ℝ) ^ k *
        ((psi n : ℝ) ^ k + (ArithmeticFunction.sigma 1 n : ℝ) ^ k))) ≥
    (4 * ((n : ℝ) - 1) ^ (2 * k) + ((n : ℝ) ^ 2 - 1) ^ k +
      ((n : ℝ) + 1) ^ (2 * k)) /
    (2 * (((n : ℝ) - 1) ^ (2 * k) + ((n : ℝ) ^ 2 - 1) ^ k))

/-- The full source inequality is an exact affine normalization of Conjecture 5. -/
theorem result : claim := by
  intro n hn k hk
  have hn0 : 0 < n := by omega
  have hphi : 0 < (Nat.totient n : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hn0)
  have hpsi_nat : 0 < psi n := by
    rw [psi_prod (by omega : n ≠ 0)]
    exact Finset.prod_pos fun p hp =>
      Nat.mul_pos (pow_pos (Nat.pos_of_mem_primeFactors hp) _) (by omega)
  have hpsi : 0 < (psi n : ℝ) := by exact_mod_cast hpsi_nat
  have hsigma : 0 < (ArithmeticFunction.sigma 1 n : ℝ) := by
    exact_mod_cast (ArithmeticFunction.sigma_pos 1 n (by omega))
  let a : ℝ := (Nat.totient n : ℝ) ^ k
  let b : ℝ := (psi n : ℝ) ^ k
  let c : ℝ := (ArithmeticFunction.sigma 1 n : ℝ) ^ k
  have ha : 0 < a := pow_pos hphi k
  have hb : 0 < b := pow_pos hpsi k
  have hc : 0 < c := pow_pos hsigma k
  have hab : a + b ≠ 0 := by positivity
  have hac : a + c ≠ 0 := by positivity
  have hbc : b + c ≠ 0 := by positivity
  have hidentity :
      (a * (b + c) + b * (a + c) + c * (a + b)) *
        (1 / (a * (b + c)) + 1 / (b * (a + c)) + 1 / (c * (a + b))) =
      6 + 2 * (a * b / (c * (a + b)) + a * c / (b * (a + c)) +
        b * c / (a * (b + c))) := by
    field_simp [ha.ne', hb.ne', hc.ne', hab, hac, hbc]
    <;> ring
  have h5 := DimitrovLowerBoundsC4C5.result5 n hn k hk
  change (a * (b + c) + b * (a + c) + c * (a + b)) *
      (1 / (a * (b + c)) + 1 / (b * (a + c)) + 1 / (c * (a + b))) ≥ _ at h5
  rw [hidentity] at h5
  have hnminus : 0 < (n : ℝ) - 1 := by
    have hcast : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hnplus : 0 < (n : ℝ) + 1 := by positivity
  have hnsq : 0 < (n : ℝ) ^ 2 - 1 := by
    nlinarith [mul_pos hnminus hnplus]
  have hden : ((n : ℝ) - 1) ^ (2 * k) + ((n : ℝ) ^ 2 - 1) ^ k ≠ 0 := by
    positivity
  have hrhs :
      (10 * ((n : ℝ) - 1) ^ (2 * k) + 7 * ((n : ℝ) ^ 2 - 1) ^ k +
        ((n : ℝ) + 1) ^ (2 * k)) /
      (((n : ℝ) - 1) ^ (2 * k) + ((n : ℝ) ^ 2 - 1) ^ k) =
      6 + 2 * ((4 * ((n : ℝ) - 1) ^ (2 * k) + ((n : ℝ) ^ 2 - 1) ^ k +
        ((n : ℝ) + 1) ^ (2 * k)) /
      (2 * (((n : ℝ) - 1) ^ (2 * k) + ((n : ℝ) ^ 2 - 1) ^ k))) := by
    field_simp [hden]
    <;> ring
  rw [hrhs] at h5
  change a * b / (c * (a + b)) + a * c / (b * (a + c)) +
    b * c / (a * (b + c)) ≥ _
  linarith

#print axioms result

end D5.S3.Arith.Divisors.DimitrovLowerBoundC6

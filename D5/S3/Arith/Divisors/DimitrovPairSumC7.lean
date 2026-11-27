/- GID: D5/S3/Arith/Divisors/DimitrovPairSumC7
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/DimitrovPairSumC7
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Powered arithmetic-function pair sums satisfy Dimitrov's seventh lower bound. -/

/-
admission_basis: open-problem-resolution (#30579; candidate Proved)
escape_witness: none
proof_shape:
  claim: bind-only source definition; consumer: result.
  result: bind-only; external endpoint: arXiv:2606.12484v1, Conjecture 7.
Direct frozen dependencies: DimitrovLowerBoundsC4C5.psi_ge,
DimitrovLowerBoundsC4C5.sigma_ge_psi, DimitrovPsiSigmaSeparation.separation,
DimitrovNesbittOppositeGap.opposite_gap.
-/

import D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5
import D5.S3.Arith.Divisors.DimitrovPsiSigmaSeparation
import D5.S3.Arith.Divisors.DimitrovNesbittOppositeGap

/-! The complete pair-sum bound follows from the ratio separation and opposite-gap Nesbitt bound. -/

set_option autoImplicit false

namespace D5.S3.Arith.Divisors.DimitrovPairSumC7

open D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes
open D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5

/-- The unchanged complete Conjecture 7 of arXiv:2606.12484v1. -/
def claim : Prop := ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k →
  let x : ℝ := (Nat.totient n : ℝ) + (psi n : ℝ)
  let y : ℝ := (Nat.totient n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ)
  let z : ℝ := (psi n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ)
  x ^ k / (y ^ k + z ^ k) + y ^ k / (x ^ k + z ^ k) +
    z ^ k / (x ^ k + y ^ k) ≥
  (4 * (n : ℝ) ^ (2 * k) + ((n : ℝ) + 1) ^ (2 * k) +
    (n : ℝ) ^ k * ((n : ℝ) + 1) ^ k) /
  (2 * ((n : ℝ) ^ (2 * k) + (n : ℝ) ^ k * ((n : ℝ) + 1) ^ k))

/-- The full source pair-sum inequality for natural numbers n ≥ 2, with real ratios and
positive natural exponents k ≥ 1. -/
theorem result : claim := by
  intro n hn k _hk
  have hp := psi_ge hn
  have hsp := sigma_ge_psi hn
  have hphi : 0 < (Nat.totient n : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < n))
  have hpsi : 0 < (psi n : ℝ) := by exact_mod_cast (show 0 < psi n by omega)
  have hsigma : 0 < (ArithmeticFunction.sigma 1 n : ℝ) := by
    exact_mod_cast (show 0 < ArithmeticFunction.sigma 1 n by omega)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let x : ℝ := (Nat.totient n : ℝ) + (psi n : ℝ)
  let y : ℝ := (Nat.totient n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ)
  let z : ℝ := (psi n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ)
  let q : ℝ := ((n : ℝ) + 1) / (n : ℝ)
  have hx : 0 < x := add_pos hphi hpsi
  have hy : 0 < y := add_pos hphi hsigma
  have hxy : x ≤ y := by dsimp [x, y]; exact_mod_cast (Nat.add_le_add_left hsp _)
  have hq : 1 ≤ q := by dsimp [q]; apply (le_div_iff₀ hn0).2; linarith
  have hqy : q * y ≤ z :=
    (le_div_iff₀ hy).mp (DimitrovPsiSigmaSeparation.separation n hn).1
  have hpowy : q ^ k * y ^ k ≤ z ^ k := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ q * y) hqy k
  have hqk : 1 ≤ q ^ k := one_le_pow₀ hq
  have hX : 0 < x ^ k := pow_pos hx k
  have hXY : x ^ k ≤ y ^ k := pow_le_pow_left₀ hx.le hxy k
  have hYZ : y ^ k ≤ z ^ k := calc
    y ^ k = 1 * y ^ k := (one_mul _).symm
    _ ≤ q ^ k * y ^ k := mul_le_mul_of_nonneg_right hqk (pow_nonneg hy.le k)
    _ ≤ z ^ k := hpowy
  have hb := (DimitrovNesbittOppositeGap.opposite_gap hX hXY hYZ hqk
    ((le_div_iff₀ (pow_pos hy k)).2 hpowy)).1
  change x ^ k / (y ^ k + z ^ k) + y ^ k / (x ^ k + z ^ k) +
    z ^ k / (x ^ k + y ^ k) ≥ _
  calc
    _ ≥ q ^ k / 2 + 2 / (q ^ k + 1) := by simpa only [add_comm (1 : ℝ) (q ^ k)] using hb
    _ = _ := by
      dsimp [q]
      rw [div_pow]
      rw [show 2 * k = k * 2 by omega]
      simp only [pow_mul]
      have hnkp : 0 < (n : ℝ) ^ k := pow_pos hn0 k
      have hnpkp : 0 < ((n : ℝ) + 1) ^ k := pow_pos (by positivity) k
      field_simp [hnkp.ne', (add_pos hnkp hnpkp).ne']
      <;> ring

#print axioms result

end D5.S3.Arith.Divisors.DimitrovPairSumC7

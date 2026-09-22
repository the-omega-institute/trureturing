/- GID: D5/S3/Arith/Congruence/SchulteHalfFactorialPrimeCriterion
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/SchulteHalfFactorialPrimeCriterion
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Schulte's A000680 half-factorial primality criterion. -/

 import D5.S3.Arith.Congruence.LaymanOddPowerFactorialResidue
 import Mathlib.Data.Nat.Factorial.DoubleFactorial

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Nat

namespace D5.S3.Arith.Congruence.SchulteHalfFactorialPrimeCriterion

/-- A000680: `(2n)! / 2^n`, with exact natural-number division. -/
def a (n : ℕ) : ℕ := (2 * n).factorial / 2 ^ n

/-- Schulte's criterion: for positive `n`, `(2n+1)` divides `a n + 2^n` exactly when it is prime. -/
theorem result (n : ℕ) (hn : 0 < n) :
    (2 * n + 1) ∣ a n + 2 ^ n ↔ (2 * n + 1).Prime := by
  have hodd : Odd (2 * n + 1) := ⟨n, by omega⟩
  have hcop_two : (2 * n + 1).Coprime 2 := hodd.coprime_two_right
  have hcop_pow : (2 * n + 1).Coprime (2 ^ n) := hcop_two.pow_right n
  have hpow_dvd : 2 ^ n ∣ (2 * n).factorial := by
    have hfac : (2 * n).factorial = (2 * n)‼ * (2 * n - 1)‼ := by
      calc
        (2 * n).factorial = ((2 * n - 1) + 1).factorial := by congr 1; omega
        _ = ((2 * n - 1) + 1)‼ * (2 * n - 1)‼ :=
          Nat.factorial_eq_mul_doubleFactorial (2 * n - 1)
        _ = (2 * n)‼ * (2 * n - 1)‼ := by
          rw [show 2 * n - 1 + 1 = 2 * n by omega]
    rw [hfac, Nat.doubleFactorial_two_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_right (2 ^ n) n.factorial) _
  have hmul_div : 2 ^ n * a n = (2 * n).factorial := by
    simpa [a] using Nat.mul_div_cancel' hpow_dvd
  constructor
  · intro hdiv
    by_contra hnprime
    have hmul : 2 * n + 1 ∣ 2 ^ n * (a n + 2 ^ n) :=
      dvd_mul_of_dvd_right hdiv (2 ^ n)
    have hsum : 2 * n + 1 ∣ (2 * n).factorial + 4 ^ n := by
      simpa [mul_add, hmul_div, ← mul_pow] using hmul
    have htri : (2 * n) * (2 * n + 1) / 2 ∣ (2 * n).factorial :=
      D5.S3.Arith.Congruence.LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime
        (by omega) (by
          intro h
          exact hnprime h.1)
    have hmod_dvd_tri : 2 * n + 1 ∣ (2 * n) * (2 * n + 1) / 2 := by
      rw [mul_comm (2 * n), Nat.mul_div_assoc (2 * n + 1) (dvd_mul_right 2 n)]
      simp
    have hfac_dvd : 2 * n + 1 ∣ (2 * n).factorial := hmod_dvd_tri.trans htri
    have hcancel_add :
        (2 * n + 1 ∣ (2 * n).factorial + 4 ^ n) ↔ (2 * n + 1 ∣ 4 ^ n) :=
      (Nat.dvd_add_iff_right hfac_dvd).symm
    have hfour_dvd : 2 * n + 1 ∣ 4 ^ n := hcancel_add.mp hsum
    have hpow_eq : 4 ^ n = 2 ^ (2 * n) := by
      calc
        4 ^ n = (2 ^ 2) ^ n := by norm_num
        _ = 2 ^ (2 * n) := by rw [pow_mul]
    have hcop_four : (2 * n + 1).Coprime (4 ^ n) := by
      rw [hpow_eq]
      exact hcop_two.pow_right (2 * n)
    have hm_one : 2 * n + 1 = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop_four dvd_rfl hfour_dvd
    omega
  · intro hp
    let _ : Fact (Nat.Prime (2 * n + 1)) := ⟨hp⟩
    have hw : (((2 * n).factorial : ℕ) : ZMod (2 * n + 1)) = -1 := by
      simpa using ZMod.wilsons_lemma (2 * n + 1)
    have htwo_ne : (2 : ZMod (2 * n + 1)) ≠ 0 := by
      intro hzero
      have hdvd : 2 * n + 1 ∣ 2 :=
        (ZMod.natCast_eq_zero_iff 2 (2 * n + 1)).mp hzero
      have hle : 2 * n + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hfermat : (2 : ZMod (2 * n + 1)) ^ (2 * n) = 1 := by
      simpa using ZMod.pow_card_sub_one_eq_one htwo_ne
    have hfour : (((4 ^ n : ℕ) : ZMod (2 * n + 1))) = 1 := by
      calc
        (((4 ^ n : ℕ) : ZMod (2 * n + 1))) = (4 : ZMod (2 * n + 1)) ^ n := by simp
        _ = ((2 : ZMod (2 * n + 1)) ^ 2) ^ n := by norm_num
        _ = (2 : ZMod (2 * n + 1)) ^ (2 * n) := by rw [pow_mul]
        _ = 1 := hfermat
    have hsum : 2 * n + 1 ∣ (2 * n).factorial + 4 ^ n := by
      rw [← ZMod.natCast_eq_zero_iff]
      simp only [Nat.cast_add, hw, hfour, neg_add_cancel]
    have hmul : 2 * n + 1 ∣ 2 ^ n * (a n + 2 ^ n) := by
      simpa [mul_add, hmul_div, ← mul_pow] using hsum
    rw [mul_comm (2 ^ n) (a n + 2 ^ n)] at hmul
    exact hcop_pow.dvd_mul_right.mp hmul

end D5.S3.Arith.Congruence.SchulteHalfFactorialPrimeCriterion

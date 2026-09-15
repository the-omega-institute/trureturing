/- GID: D5/S3/Arith/Congruence/PricePrimeQuotientExponent
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/PricePrimeQuotientExponent
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum, mathlib/module/Mathlib.Data.Nat.GCD.Basic, mathlib/module/Mathlib.Data.Nat.Prime.Basic, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Price's A228558 and A231329 prime quotients can occur only at prime exponents. -/

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.PricePrimeQuotientExponent

theorem prime_quotient_exponent_is_prime
    {x y k : ℕ} (hy : 1 ≤ y) (hxy : y < x) (hcop : Nat.Coprime x y)
    (hdvd : x + y ∣ x ^ k + y ^ k)
    (hp : Nat.Prime ((x ^ k + y ^ k) / (x + y))) :
    Nat.Prime k := by
  have hx : 2 ≤ x := by omega
  have hsum : 3 ≤ x + y := by omega
  have hkodd : Odd k := by
    rw [← Nat.not_even_iff_odd]
    intro hkeven
    have hsumZ : ((x + y : ℕ) : ℤ) ∣ ((x ^ k + y ^ k : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr hdvd
    have hdiffZ : ((x + y : ℕ) : ℤ) ∣
        ((x ^ k : ℕ) : ℤ) - ((y ^ k : ℕ) : ℤ) := by
      simpa [hkeven.neg_pow] using
        (sub_dvd_pow_sub_pow (x : ℤ) (-(y : ℤ)) k)
    have htwoZ : ((x + y : ℕ) : ℤ) ∣ ((2 * y ^ k : ℕ) : ℤ) := by
      have hraw := dvd_sub hsumZ hdiffZ
      have heq :
          ((x ^ k + y ^ k : ℕ) : ℤ) -
              (((x ^ k : ℕ) : ℤ) - ((y ^ k : ℕ) : ℤ)) =
            ((2 * y ^ k : ℕ) : ℤ) := by
        push_cast
        ring
      rwa [heq] at hraw
    have htwo : x + y ∣ 2 * y ^ k := Int.natCast_dvd_natCast.mp htwoZ
    have hcop' : Nat.Coprime (x + y) (y ^ k) :=
      ((Nat.coprime_add_self_left).2 hcop).pow_right k
    have : x + y ∣ 2 := (hcop'.dvd_mul_right).mp htwo
    have := Nat.le_of_dvd (by decide : 0 < 2) this
    omega
  have hk1 : k ≠ 1 := by
    intro hk
    subst k
    have : Nat.Prime 1 := by
      simpa [Nat.div_self (by omega : 0 < x + y)] using hp
    exact Nat.not_prime_one this
  have hk2 : 2 ≤ k := by
    obtain ⟨j, hj⟩ := hkodd
    omega
  by_contra hkprime
  obtain ⟨d, hdk, hd2, hdklt⟩ := Nat.exists_dvd_of_not_prime2 hk2 hkprime
  obtain ⟨m, hkm⟩ := hdk
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hkm
    omega
  have hm1 : m ≠ 1 := by
    rintro rfl
    simp at hkm
    omega
  have hm2 : 2 ≤ m := by omega
  have hm_lt_k : m < k := by
    rw [hkm]
    exact lt_mul_of_one_lt_left (by omega) (by omega)
  have hdodd : Odd d := by
    apply Nat.Odd.of_mul_left
    rwa [← hkm]
  have hmodd : Odd m := by
    apply Nat.Odd.of_mul_right
    rwa [← hkm]
  have hsmall : x + y ∣ x ^ d + y ^ d :=
    hdodd.nat_add_dvd_pow_add_pow x y
  have hlarge : x ^ d + y ^ d ∣ x ^ k + y ^ k := by
    simpa [hkm, pow_mul] using
      (hmodd.nat_add_dvd_pow_add_pow (x ^ d) (y ^ d))
  have hsum_lt_small : x + y < x ^ d + y ^ d := by
    apply Nat.add_lt_add_of_lt_of_le
    · simpa only [pow_one] using
        (Nat.pow_lt_pow_iff_right (by omega : 1 < x)).2 (show 1 < d by omega)
    · simpa only [pow_one] using
        Nat.pow_le_pow_right (by omega : 0 < y) (show 1 ≤ d by omega)
  have hsmall_lt_large : x ^ d + y ^ d < x ^ k + y ^ k := by
    apply Nat.add_lt_add_of_lt_of_le
    · exact (Nat.pow_lt_pow_iff_right (by omega : 1 < x)).2 hdklt
    · exact Nat.pow_le_pow_right (by omega : 0 < y) hdklt.le
  have hfactor1 : (x ^ k + y ^ k) / (x ^ d + y ^ d) ≠ 1 := by
    intro h
    have := Nat.eq_of_dvd_of_div_eq_one hlarge h
    omega
  have hfactor2 : (x ^ d + y ^ d) / (x + y) ≠ 1 := by
    intro h
    have := Nat.eq_of_dvd_of_div_eq_one hsmall h
    omega
  have hproduct :
      ((x ^ k + y ^ k) / (x ^ d + y ^ d)) *
          ((x ^ d + y ^ d) / (x + y)) =
        (x ^ k + y ^ k) / (x + y) :=
    Nat.div_mul_div hlarge hsmall
  exact (Nat.not_prime_of_mul_eq hproduct hfactor1 hfactor2) hp

theorem result_a228558 (k : ℕ)
    (hdvd : 21 ∣ 17 ^ k + 4 ^ k)
    (hp : Nat.Prime ((17 ^ k + 4 ^ k) / 21)) :
    Nat.Prime k := by
  apply prime_quotient_exponent_is_prime (x := 17) (y := 4) (k := k)
  · norm_num
  · norm_num
  · decide
  · simpa using hdvd
  · simpa using hp

theorem result_a231329 (k : ℕ)
    (hdvd : 23 ∣ 19 ^ k + 4 ^ k)
    (hp : Nat.Prime ((19 ^ k + 4 ^ k) / 23)) :
    Nat.Prime k := by
  apply prime_quotient_exponent_is_prime (x := 19) (y := 4) (k := k)
  · norm_num
  · norm_num
  · decide
  · simpa using hdvd
  · simpa using hp

#print axioms prime_quotient_exponent_is_prime
#print axioms result_a228558
#print axioms result_a231329

end D5.S3.Arith.Congruence.PricePrimeQuotientExponent

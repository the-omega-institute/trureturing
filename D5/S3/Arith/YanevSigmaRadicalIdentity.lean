/- GID: D5/S3/Arith/YanevSigmaRadicalIdentity
   generality: I
   mirror-B: D5/B/S3/Arith/YanevSigmaRadicalIdentity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Yanev's radical identity expresses every positive divisor-power sum as a divisor-sum ratio. -/

import D5.S1.Deficit.AlmostAdditivity
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.Radical.NatInt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.YanevSigmaRadicalIdentity

open ArithmeticFunction
open D5.S1.Deficit.AlmostAdditivity (primeRadical)
open scoped ArithmeticFunction.sigma

theorem result (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    σ m n * σ 1 (primeRadical n ^ (m - 1)) = σ 1 (n ^ m * primeRadical n ^ (m - 1)) := by
  simp only [primeRadical, ← Nat.radical_eq_prod_primeFactors]
  clear hn
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp [zero_pow hm.ne']
  | one => simp
  | prime_pow p e hp he =>
    rw [UniqueFactorizationMonoid.radical_pow_of_prime hp.prime he.ne']
    simp only [normalize_eq]
    rw [sigma_apply_prime_pow hp, sigma_one_apply_prime_pow hp,
      ← pow_mul, ← pow_add, sigma_one_apply_prime_pow hp]
    have hlen : e * m + (m - 1) + 1 = (e + 1) * m := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [Nat.sub_add_cancel hm, hlen]
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
    have hpm : 0 < p ^ m := pow_pos hp.pos m
    have hpm1 : p ^ m - 1 + 1 = p ^ m := Nat.sub_add_cancel hpm
    have hfirst := geom_sum_mul_add (p ^ m - 1) (e + 1)
    have hsecond := geom_sum_mul_add (p - 1) m
    have hwhole := geom_sum_mul_add (p - 1) ((e + 1) * m)
    simp only [hp1] at hsecond hwhole
    simp only [hpm1, ← pow_mul, Nat.mul_comm m] at hfirst
    have hcancel : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
    have hsecond' : (∑ x ∈ Finset.range m, p ^ x) * (p - 1) = p ^ m - 1 := by
      omega
    apply Nat.eq_of_mul_eq_mul_right hcancel
    rw [mul_assoc, hsecond']
    omega
  | coprime a b ha hb hab iha ihb =>
    have hrad : Nat.Coprime (UniqueFactorizationMonoid.radical a)
        (UniqueFactorizationMonoid.radical b) :=
      hab.of_dvd UniqueFactorizationMonoid.radical_dvd_self
        UniqueFactorizationMonoid.radical_dvd_self
    have harb : Nat.Coprime a (UniqueFactorizationMonoid.radical b) :=
      hab.of_dvd_right UniqueFactorizationMonoid.radical_dvd_self
    have hrab : Nat.Coprime (UniqueFactorizationMonoid.radical a) b :=
      hab.of_dvd_left UniqueFactorizationMonoid.radical_dvd_self
    have htrans : Nat.Coprime
        (a ^ m * UniqueFactorizationMonoid.radical a ^ (m - 1))
        (b ^ m * UniqueFactorizationMonoid.radical b ^ (m - 1)) :=
      ((hab.pow _ _).mul_right (harb.pow _ _)).mul_left
        ((hrab.pow _ _).mul_right (hrad.pow _ _))
    rw [UniqueFactorizationMonoid.radical_mul (Nat.coprime_iff_isRelPrime.mp hab), mul_pow,
      isMultiplicative_sigma.map_mul_of_coprime hab,
      isMultiplicative_sigma.map_mul_of_coprime (hrad.pow _ _), mul_pow,
      mul_mul_mul_comm (a ^ m), isMultiplicative_sigma.map_mul_of_coprime htrans]
    rw [← iha, ← ihb]
    ring

end D5.S3.Arith.YanevSigmaRadicalIdentity

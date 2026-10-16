/- GID: D5/S3/Arith/MoebiusLogarithmic/CoprimeConvolution
   generality: G
   mirror-B: D5/B/S3/Arith/MoebiusLogarithmic/CoprimeConvolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Moebius]
   utility: none
   digest: Summing the Moebius function over all supported prime powers removes their prime divisors. -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

open scoped BigOperators ArithmeticFunction.zeta
open Finset ArithmeticFunction

noncomputable section
attribute [local instance] Classical.propDecidable
namespace D5.S3.Arith.MoebiusLogarithmic

/-- Every prime factor of `n` also divides `q`, with no bound on its exponent. -/
def PrimeSupported (q n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ∣ q

private theorem primeSupported_mul (q a b : ℕ) :
    PrimeSupported q (a * b) ↔ PrimeSupported q a ∧ PrimeSupported q b := by
  constructor
  · intro h
    exact ⟨fun p hp hd => h p hp (hd.trans (dvd_mul_right a b)),
      fun p hp hd => h p hp (hd.trans (dvd_mul_left b a))⟩
  · rintro ⟨ha, hb⟩ p hp hd
    exact (hp.dvd_mul.mp hd).elim (ha p hp) (hb p hp)

private theorem primeSupported_one (q : ℕ) : PrimeSupported q 1 := by
  intro p hp hd
  exact (hp.not_dvd_one hd).elim

private theorem primeSupported_prime_pow (q p k : ℕ) (hp : p.Prime) :
    PrimeSupported q (p ^ k) ↔ k = 0 ∨ p ∣ q := by
  by_cases hk : k = 0
  · simp [hk, primeSupported_one]
  constructor
  · intro h
    exact Or.inr (h p hp (dvd_pow_self p hk))
  · rintro (h | h)
    · exact (hk h).elim
    · intro r hr hd
      have he : r = p := Nat.prime_eq_prime_of_dvd_pow hr hp hd
      simpa [he] using h

private def supportedFunction (q : ℕ) : ArithmeticFunction ℤ where
  toFun n := if n = 0 then 0 else if PrimeSupported q n then 1 else 0
  map_zero' := by simp

private def coprimeMoebius (q : ℕ) : ArithmeticFunction ℤ where
  toFun n := if n.Coprime q then ArithmeticFunction.moebius n else 0
  map_zero' := by simp

private theorem supported_multiplicative (q : ℕ) :
    IsMultiplicative (supportedFunction q) := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp [supportedFunction, primeSupported_one]
  · intro a b ha hb hab
    by_cases hqa : PrimeSupported q a <;> by_cases hqb : PrimeSupported q b <;>
      simp [supportedFunction, mul_ne_zero ha hb, ha, hb, primeSupported_mul, hqa, hqb]

private theorem coprimeMoebius_multiplicative (q : ℕ) :
    IsMultiplicative (coprimeMoebius q) := by
  constructor
  · simp [coprimeMoebius]
  · intro a b hab
    change (if (a * b).Coprime q then ArithmeticFunction.moebius (a * b) else 0) =
      (if a.Coprime q then ArithmeticFunction.moebius a else 0) *
        (if b.Coprime q then ArithmeticFunction.moebius b else 0)
    simp only [Nat.coprime_mul_iff_left,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab]
    split_ifs <;> simp_all

private theorem supported_convolution (q : ℕ) :
    supportedFunction q * ArithmeticFunction.moebius = coprimeMoebius q := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((supported_multiplicative q).mul ArithmeticFunction.isMultiplicative_moebius) _
    (coprimeMoebius_multiplicative q)).mpr
  intro p k hp
  by_cases hk : k = 0
  · rw [hk, pow_zero, ArithmeticFunction.mul_apply_one]
    simp [supportedFunction, coprimeMoebius, primeSupported_one]
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  by_cases hpq : p ∣ q
  · have hc : ¬ (p ^ k).Coprime q := by
      rw [Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hk),
        hp.coprime_iff_not_dvd]
      exact not_not.mpr hpq
    have he : (supportedFunction q * ArithmeticFunction.moebius) (p ^ k) =
        (ζ * ArithmeticFunction.moebius : ArithmeticFunction ℤ) (p ^ k) := by
      simp only [ArithmeticFunction.mul_apply]
      rw [Nat.sum_divisorsAntidiagonal
        (fun a b => supportedFunction q a * ArithmeticFunction.moebius b),
        Nat.sum_divisorsAntidiagonal
          (fun a b => ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) a) * ArithmeticFunction.moebius b)]
      simp only [Nat.sum_divisors_prime_pow hp]
      apply sum_congr rfl
      intro i hi
      simp [supportedFunction, pow_ne_zero i hp.ne_zero,
        (primeSupported_prime_pow q p i hp).mpr (Or.inr hpq)]
    rw [he, ArithmeticFunction.coe_zeta_mul_moebius]
    simp [coprimeMoebius, hc, ArithmeticFunction.one_apply, hp.ne_one, hk]
  · have hc : (p ^ k).Coprime q :=
      (hp.coprime_iff_not_dvd.mpr hpq).pow_left k
    simp only [ArithmeticFunction.mul_apply]
    rw [Nat.sum_divisorsAntidiagonal
      (fun a b => supportedFunction q a * ArithmeticFunction.moebius b)]
    simp only [Nat.sum_divisors_prime_pow hp]
    rw [sum_eq_single 0]
    · simp [supportedFunction, primeSupported_one, coprimeMoebius, hc]
    · intro i hi hi0
      simp [supportedFunction, pow_ne_zero i hp.ne_zero,
        primeSupported_prime_pow q p i hp, hi0, hpq]
    · simp

/-- Exact coprime coefficients, including every allowed prime-power divisor. -/
theorem sum_supported_moebius (q n : ℕ) :
    (∑ d ∈ n.divisors.filter (PrimeSupported q), ArithmeticFunction.moebius (n / d)) =
      if n.Coprime q then ArithmeticFunction.moebius n else 0 := by
  classical
  have he := congrArg (fun f : ArithmeticFunction ℤ => f n) (supported_convolution q)
  simp only [ArithmeticFunction.mul_apply] at he
  rw [Nat.sum_divisorsAntidiagonal
    (fun a b => supportedFunction q a * ArithmeticFunction.moebius b)] at he
  change (∑ d ∈ n.divisors, supportedFunction q d * ArithmeticFunction.moebius (n / d)) =
    (if n.Coprime q then ArithmeticFunction.moebius n else 0) at he
  rw [sum_filter]
  convert he using 1
  apply sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  by_cases h : PrimeSupported q d <;> simp [supportedFunction, hd0, h]

#print axioms sum_supported_moebius
end D5.S3.Arith.MoebiusLogarithmic

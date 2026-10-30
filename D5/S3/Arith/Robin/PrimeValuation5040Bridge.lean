/- GID: D5/S3/Arith/Robin/PrimeValuation5040Bridge
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PrimeValuation5040Bridge
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The 5040 divisibility block is the exact simultaneous valuation fibre for the four primes 2, 3, 5, and 7. -/

/- The finite valuation calculation is adapted from the OpenAI/math arithmetic-research
source `WUnitValuationLaw.lean` (SHA256
68662b3aaae7788b7a7a552578f6a27d4e7b822f6e97aaebd81de60f54b62c19). This file keeps
only the natural-number factorisation content needed by the Robin/5040 development;
no analytic claim about RH is made here. -/

import D5.S3.Arith.GoldenResource5040PriceInterval
import D5.S3.Arith.GoldenResource.GoldenDivisorLanguage
import D5.S3.Factorization.PrimePowers.FiniteCrtJoin
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PrimeValuation5040Bridge

open scoped BigOperators
open D5.S3.Arith.GoldenResource5040PriceInterval
open D5.S3.Arith.GoldenResource.GoldenDivisorLanguage
open D5.S3.Factorization.PrimePowers.FiniteCrtJoin

/-- The square-free modulus carried by a finite prime support. -/
def primeModulus (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

/-- A simultaneous valuation fibre, including the unit condition. -/
def jointFiber (S : Finset ℕ) (a : ℕ → ℕ) (W n : ℕ) : Prop :=
  n ≠ 0 ∧ n.Coprime W ∧ ∀ p ∈ S, n.factorization p = a p

theorem primeBlock_pos {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (a : ℕ → ℕ) :
    0 < primePowerProduct S a := by
  exact Finset.prod_pos (fun p hp => pow_pos (hS p hp).pos _)

theorem primeBlock_factorization {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : ℕ → ℕ) (r : ℕ) :
    (primePowerProduct S a).factorization r = if r ∈ S then a r else 0 := by
  classical
  unfold primePowerProduct
  rw [Nat.factorization_prod_apply (fun p hp => pow_ne_zero _ (hS p hp).ne_zero)]
  have he : (∑ p ∈ S, (p ^ a p).factorization r) =
      ∑ p ∈ S, (Finsupp.single p (a p)) r := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [(hS p hp).factorization_pow]
  rw [he]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq']

theorem primeBlock_coprime {S : Finset ℕ} {W : ℕ}
    (hW : ∀ p ∈ S, p.Coprime W) (a : ℕ → ℕ) :
    (primePowerProduct S a).Coprime W := by
  rw [primePowerProduct, Nat.coprime_prod_left_iff]
  intro p hp
  exact (hW p hp).pow_left _

theorem jointFiber_mul_iff {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : ℕ → ℕ) {W : ℕ} (hW : ∀ p ∈ S, p.Coprime W) (n : ℕ) :
    jointFiber S a W (primePowerProduct S a * n) ↔
      n ≠ 0 ∧ n.Coprime (W * primeModulus S) := by
  classical
  have hd0 := ne_of_gt (primeBlock_pos hS a)
  have hdc := primeBlock_coprime hW a
  constructor
  · rintro ⟨hn, hc, hv⟩
    have hn0 : n ≠ 0 := right_ne_zero_of_mul hn
    refine ⟨hn0, Nat.coprime_mul_iff_right.mpr ⟨(Nat.coprime_mul_iff_left.mp hc).2, ?_⟩⟩
    rw [primeModulus, Nat.coprime_prod_right_iff]
    intro p hp
    have he := hv p hp
    rw [Nat.factorization_mul hd0 hn0, Finsupp.add_apply,
      primeBlock_factorization hS a p, if_pos hp] at he
    have hz : n.factorization p = 0 := by omega
    apply Nat.Coprime.symm
    apply (hS p hp).coprime_iff_not_dvd.mpr
    exact (((Nat.factorization_eq_zero_iff n p).mp hz).resolve_left
      (fun h => h (hS p hp))).resolve_right hn0
  · rintro ⟨hn0, hc⟩
    have hnc : n.Coprime W := (Nat.coprime_mul_iff_right.mp hc).1
    have hnp : n.Coprime (primeModulus S) := (Nat.coprime_mul_iff_right.mp hc).2
    refine ⟨mul_ne_zero hd0 hn0, hdc.mul_left hnc, ?_⟩
    intro p hp
    have hcprime : n.Coprime p :=
      (Nat.coprime_prod_right_iff.mp hnp) p hp
    have hnd : ¬p ∣ n := (hS p hp).coprime_iff_not_dvd.mp hcprime.symm
    have hz : n.factorization p = 0 := by simp [Nat.factorization_eq_zero_iff, hnd]
    rw [Nat.factorization_mul hd0 hn0, Finsupp.add_apply,
      primeBlock_factorization hS a p, if_pos hp, hz, add_zero]

private theorem primeSupport5040_prime :
    ∀ p ∈ _root_.D5.S3.Arith.GoldenResource.GoldenDivisorLanguage.primes5040,
      p.Prime := by
  decide

/-- The valuation profile of 5040, shared with the golden-resource development. -/
def profile5040 (p : ℕ) : ℕ := targetExponent5040 p

theorem profile5040_eq_factorization (p : ℕ) :
    profile5040 p = (5040 : ℕ).factorization p := by
  exact target_exponent_eq_factorization_5040 p

theorem primePowerProduct_5040 :
    primePowerProduct
      _root_.D5.S3.Arith.GoldenResource.GoldenDivisorLanguage.primes5040 profile5040 = 5040 := by
  decide

theorem primeModulus_5040 :
    primeModulus
      _root_.D5.S3.Arith.GoldenResource.GoldenDivisorLanguage.primes5040 = 210 := by
  norm_num [primeModulus,
    _root_.D5.S3.Arith.GoldenResource.GoldenDivisorLanguage.primes5040]

/--
The exact 5040 valuation fibre.  After extracting the fixed block `5040`, the
remaining factor is precisely a nonzero integer coprime to both the external
unit modulus and `210 = 2*3*5*7`.  This is the finite arithmetic bridge used
by the Robin records: the divisibility conclusion identifies the block, and
this theorem identifies all residual integers with the same four valuations.
-/
theorem jointFiber5040_mul_iff {W n : ℕ}
    (hW : ∀ p ∈ _root_.D5.S3.Arith.GoldenResource.GoldenDivisorLanguage.primes5040,
      p.Coprime W) :
    jointFiber _root_.D5.S3.Arith.GoldenResource.GoldenDivisorLanguage.primes5040
      profile5040 W (5040 * n) ↔
      n ≠ 0 ∧ n.Coprime (W * 210) := by
  rw [← primePowerProduct_5040,
    jointFiber_mul_iff primeSupport5040_prime profile5040 hW n,
    primeModulus_5040]

end D5.S3.Arith.Robin.PrimeValuation5040Bridge

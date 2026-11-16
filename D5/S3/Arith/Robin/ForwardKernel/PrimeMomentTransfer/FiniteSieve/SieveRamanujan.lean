/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRamanujan
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRamanujan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ramanujan sums and additive character orthogonality identify finite sieve frequencies. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveKuperbergDefs
import Mathlib.Analysis.Fourier.ZMod
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.RamanujanSums
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.TotientPrimeProducts

/-! Additive phases and the squarefree divisor expansion of the reduced-residue indicator. -/

open scoped BigOperators
open Finset
open D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- The positive exponential phase respects addition of real frequencies. -/
theorem sieve_character_add (u v : ℝ) :
    unitCharacter (u + v) = unitCharacter u * unitCharacter v := by
  unfold unitCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Every divisor frequency can be expressed over the original modulus. -/
private theorem sieve_common_frequency (k : ℕ) (Q : ℕ+) (q r : Fin k → ℕ)
    (hq : ∀ i, q i ∣ (Q : ℕ)) (hpos : ∀ i, 0 < q i) :
    ∃ t : ℤ, (∑ i, (r i : ℚ) / (q i : ℚ)) = (t : ℚ) / (Q : ℚ) := by
  refine ⟨∑ i, (r i : ℤ) * ((Q : ℕ) / q i : ℕ), ?_⟩
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (q i : ℚ) ≠ 0 := by exact_mod_cast (hpos i).ne'
  have hQ : (Q : ℚ) ≠ 0 := by exact_mod_cast Q.ne_zero
  have he : (q i : ℚ) * (((Q : ℕ) / q i : ℕ) : ℚ) = (Q : ℚ) := by
    exact_mod_cast Nat.mul_div_cancel' (hq i)
  rw [div_eq_div_iff hi hQ, ← he]
  ring

/-- Averaging an integer frequency gives its divisibility indicator. -/
private theorem sieve_integer_frequency (Q : ℕ+) (t : ℤ) :
    (∑ x : ZMod (Q : ℕ), unitCharacter ((x.val : ℝ) * t / (Q : ℝ))) / (Q : ℂ) =
      if (Q : ℤ) ∣ t then 1 else 0 := by
  classical
  have hterm (x : ZMod (Q : ℕ)) :
      unitCharacter ((x.val : ℝ) * t / (Q : ℝ)) = ZMod.stdAddChar (x * (t : ZMod (Q : ℕ))) := by
    have he : x * (t : ZMod (Q : ℕ)) = (((x.val : ℤ) * t : ℤ) : ZMod (Q : ℕ)) := by
      simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [he, ZMod.stdAddChar_coe]
    unfold unitCharacter
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar (Q : ℕ))]
  simp only [ZMod.card, ZMod.intCast_zmod_eq_zero_iff_dvd]
  split_ifs <;> simp [Q.ne_zero]

open Classical in
/-- A uniform residue average selects exactly the integral total frequencies. -/
theorem sieve_character_orthogonality (k : ℕ) (Q : ℕ+) (q : Fin k → ℕ)
    (hq : ∀ i, q i ∣ (Q : ℕ)) (hpos : ∀ i, 0 < q i) (r : Fin k → ℕ) :
    (∑ x : ZMod (Q : ℕ), unitCharacter ((x.val : ℝ) * ∑ i, (r i : ℝ) / q i)) / (Q : ℂ) =
      if (∑ i, (r i : ℚ) / (q i : ℚ)) ∈ Set.range (fun z : ℤ => (z : ℚ)) then 1 else 0 := by
  classical
  obtain ⟨t, ht⟩ := sieve_common_frequency k Q q r hq hpos
  have hr : (∑ i, (r i : ℝ) / (q i : ℝ)) = (t : ℝ) / (Q : ℝ) := by
    have he := congrArg (fun a : ℚ => (a : ℝ)) ht
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_natCast, Rat.cast_intCast] using he
  have hQ : (Q : ℚ) ≠ 0 := by exact_mod_cast Q.ne_zero
  have hi : (t : ℚ) / (Q : ℚ) ∈ Set.range (fun z : ℤ => (z : ℚ)) ↔ (Q : ℤ) ∣ t := by
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      change (z : ℚ) = (t : ℚ) / (Q : ℚ) at hz
      have he : (t : ℚ) = (Q : ℚ) * (z : ℚ) := ((eq_div_iff hQ).mp hz).symm.trans (mul_comm _ _)
      exact_mod_cast he
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      apply (eq_div_iff hQ).mpr
      change (z : ℚ) * (Q : ℚ) = (t : ℚ)
      exact_mod_cast (mul_comm z (Q : ℤ)).trans hz.symm
  simp_rw [hr, ← mul_div_assoc]
  rw [sieve_integer_frequency, ht, hi]
  split_ifs <;> rfl

private theorem sieve_ramanujan_prime (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ramanujanSum p n = if p ∣ n then (p : ℂ) - 1 else -1 := by
  have h := D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.RamanujanSums.ramanujan_prime_power p n 0 hp
  simp only [zero_add, pow_one, pow_zero, one_dvd, ite_true] at h
  split_ifs with hn
  · simpa only [ite_eq_left hn] using h
  · simpa only [ite_eq_right hn, zero_sub] using h

private theorem sieve_ramanujan_divisor_product (Q : ℕ+) (hQ : Squarefree (Q : ℕ)) (n : ℕ) :
    (∑ q ∈ (Q : ℕ).divisors,
      (ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ) * ramanujanSum q n) =
      ∏ p ∈ (Q : ℕ).primeFactors, (1 - ramanujanSum p n / (p - 1 : ℂ)) := by
  let F : ArithmeticFunction ℂ :=
    ⟨fun q => (ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ) * ramanujanSum q n,
      by simp [ramanujanSum]⟩
  have hF : F.IsMultiplicative := by
    constructor
    · simp [F, ramanujanSum]
    · intro a b hab
      change (ArithmeticFunction.moebius (a * b) : ℂ) / (Nat.totient (a * b) : ℂ) *
        ramanujanSum (a * b) n =
        ((ArithmeticFunction.moebius a : ℂ) / (Nat.totient a : ℂ) * ramanujanSum a n) *
          ((ArithmeticFunction.moebius b : ℂ) / (Nat.totient b : ℂ) * ramanujanSum b n)
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab,
        Nat.totient_mul hab,
        D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.RamanujanSums.ramanujan_multiplicative a b n hab]
      push_cast
      ring
  change (∑ q ∈ (Q : ℕ).divisors, F q) = _
  rw [← hF.prodPrimeFactors_one_add_of_squarefree hQ]
  apply Finset.prod_congr rfl
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  change 1 + (ArithmeticFunction.moebius p : ℂ) / (Nat.totient p : ℂ) * ramanujanSum p n = _
  rw [ArithmeticFunction.moebius_apply_prime hp', Nat.totient_prime hp',
    Nat.cast_sub hp'.one_le, Nat.cast_one]
  push_cast
  ring

private theorem sieve_density_prime_product (Q : ℕ+) :
    (sieveDensity Q : ℂ) =
      ∏ p ∈ (Q : ℕ).primeFactors, (p : ℂ) / (p - 1 : ℂ) := by
  unfold sieveDensity
  rw [D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.TotientPrimeProducts.totient_prime_product Q.pos]
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp'.ne_zero
  have hp1 : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp'.ne_one)
  field_simp

private theorem sieve_local_indicator_product (Q : ℕ+) (n : ℕ) :
    (∏ p ∈ (Q : ℕ).primeFactors, (1 - ramanujanSum p n / (p - 1 : ℂ))) =
      (sieveDensity Q : ℂ) * (if n.Coprime (Q : ℕ) then 1 else 0) := by
  by_cases hn : n.Coprime (Q : ℕ)
  · rw [ite_eq_left hn, mul_one, sieve_density_prime_product]
    apply Finset.prod_congr rfl
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hpn : ¬p ∣ n := fun h =>
      (Nat.not_coprime_of_dvd_of_dvd hp'.one_lt h (Nat.dvd_of_mem_primeFactors hp)) hn
    have hp1 : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp'.ne_one)
    rw [sieve_ramanujan_prime p hp' n, ite_eq_right hpn]
    field_simp
    ring
  · rw [ite_eq_right hn, mul_zero]
    obtain ⟨p, hp, hpn, hpQ⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hmem : p ∈ (Q : ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpQ, Q.ne_zero⟩
    apply Finset.prod_eq_zero hmem
    have hp1 : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
    rw [sieve_ramanujan_prime p hp n, ite_eq_left hpn, div_self hp1, sub_self]

private theorem sieve_ramanujan_expansion (Q : ℕ+) (hQ : Squarefree (Q : ℕ)) (n : ℕ) :
    ((sieveVariable Q n 0 + 1 : ℝ) : ℂ) =
      ∑ q ∈ (Q : ℕ).divisors,
        (ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ) * ramanujanSum q n := by
  rw [sieve_ramanujan_divisor_product Q hQ n, sieve_local_indicator_product]
  have hc : (n % (Q : ℕ)).Coprime (Q : ℕ) ↔ n.Coprime (Q : ℕ) := by
    change Nat.gcd (n % (Q : ℕ)) (Q : ℕ) = 1 ↔ Nat.gcd n (Q : ℕ) = 1
    rw [← Nat.gcd_rec (Q : ℕ) n, Nat.gcd_comm (Q : ℕ) n]
  simp only [sieveVariable, zero_add, ZMod.val_natCast, hc, sub_add_cancel]
  split_ifs <;> simp

/-- The centred reduced-residue indicator has exactly the nontrivial divisor frequencies. -/
theorem sieve_centered_ramanujan_expansion (Q : ℕ+) (hQ : Squarefree (Q : ℕ))
    (d : ℕ) (x : ZMod (Q : ℕ)) :
    (sieveVariable Q d x : ℂ) =
      ∑ q ∈ (Q : ℕ).divisors.erase 1,
        (ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ) * ramanujanSum q (x.val + d) := by
  have h := sieve_ramanujan_expansion Q hQ (x.val + d)
  have hx : sieveVariable Q (x.val + d) 0 = sieveVariable Q d x := by
    simp only [sieveVariable, zero_add, Nat.cast_add, ZMod.natCast_zmod_val]
  rw [hx] at h
  have h1 : (ArithmeticFunction.moebius 1 : ℂ) / (Nat.totient 1 : ℂ) *
      ramanujanSum 1 (x.val + d) = 1 := by
    rw [D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.RamanujanSums.ramanujan_one]
    norm_num
  have he := Finset.sum_erase_add (Q : ℕ).divisors
    (fun q => (ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ) *
      ramanujanSum q (x.val + d)) (Nat.one_mem_divisors.mpr Q.ne_zero)
  rw [h1, ← h] at he
  push_cast at he
  exact (add_right_cancel he).symm

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

/- GID: D5/S3/Factorization/PrimePowers/NoiselessPrimeSeparation
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/NoiselessPrimeSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime congruence separates exactly off divisors; degenerate gaps are audited. -/

/- Library-search audit trail (2026-08-25):
   * `git grep -liE 'ModEq|CRT|chineseRemainder' D5` found related CRT and
     residue modules, especially `ResidueSeparation` and `PrimeAxisEscape`, but
     no existing declaration packages the four divisor criteria proved here.
   * Pinned Mathlib exact hits `Int.modEq_iff_dvd`, `Int.natCast_dvd`,
     `Nat.exists_infinite_primes`, `Nat.mem_primeFactors_of_ne_zero`, and
     `Nat.infinite_setOf_prime`; the proofs below use these rather than reproving them.
   * Searches for `Kakutani` in both `D5` and pinned Mathlib returned no hits.
     Therefore the noisy product-measure equivalence/singularity side is explicitly
     out of scope: formalizing it here would create the prohibited missing domain.
   * The source states no independent definition, so this module adds no accounting-only
     definition. The finite exceptional set is expressed directly in its theorem. -/

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.NoiselessPrimeSeparation

/-!
This module formalizes only the noiseless sentence of FPOD principle 233.1. The
noisy evidence-series claim requires the absent Kakutani dichotomy for two product
measures, so no declaration below claims to cover it.

The integers avoid truncated natural subtraction. Prime moduli are natural numbers
cast to `Int`. Primality is needed only to produce a prime in the existence theorem
and to name the exceptional set in the finiteness theorem. The two pointwise divisor
criteria hold for every natural modulus, including zero and one.
-/

/-- Every modulus not dividing the integer difference distinguishes the two integers.
Primality and a lower bound on the modulus are unnecessary. -/
theorem nondividing_modulus_separates (p : Nat) (n m : Int)
    (hnotdvd : ¬ (p : Int) ∣ n - m) :
    ¬ Int.ModEq (p : Int) n m := by
  intro hmod
  exact hnotdvd (Int.modEq_iff_dvd.mp hmod.symm)

#print axioms nondividing_modulus_separates

/-- Every modulus dividing the integer difference fails to distinguish the integers.
Primality is again unnecessary. -/
theorem dividing_modulus_does_not_separate (p : Nat) (n m : Int)
    (hdvd : (p : Int) ∣ n - m) :
    Int.ModEq (p : Int) n m := by
  exact (Int.modEq_iff_dvd.mpr hdvd).symm

#print axioms dividing_modulus_does_not_separate

/-- Two distinct integers are distinguished modulo at least one natural prime. -/
theorem distinct_integers_have_distinguishing_prime (n m : Int) (hne : n ≠ m) :
    ∃ p : Nat, Nat.Prime p ∧ ¬ Int.ModEq (p : Int) n m := by
  have hdiff : (n - m).natAbs ≠ 0 := by
    simpa only [Int.natAbs_ne_zero, sub_ne_zero] using hne
  obtain ⟨p, hpLarge, hpPrime⟩ :=
    Nat.exists_infinite_primes ((n - m).natAbs + 1)
  refine ⟨p, hpPrime, nondividing_modulus_separates p n m ?_⟩
  intro hpDvd
  have hpDvdAbs : p ∣ (n - m).natAbs := Int.natCast_dvd.mp hpDvd
  have hpLe : p ≤ (n - m).natAbs :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hdiff) hpDvdAbs
  omega

#print axioms distinct_integers_have_distinguishing_prime

private lemma mem_primeFactors_iff_indistinguishing
    (n m : Int) (hne : n ≠ m) (p : Nat) :
    p ∈ (n - m).natAbs.primeFactors ↔
      Nat.Prime p ∧ Int.ModEq (p : Int) n m := by
  have hdiff : (n - m).natAbs ≠ 0 := by
    simpa only [Int.natAbs_ne_zero, sub_ne_zero] using hne
  rw [Nat.mem_primeFactors_of_ne_zero hdiff]
  constructor
  · rintro ⟨hpPrime, hpDvd⟩
    exact ⟨hpPrime, dividing_modulus_does_not_separate p n m
      (Int.natCast_dvd.mpr hpDvd)⟩
  · rintro ⟨hpPrime, hmod⟩
    exact ⟨hpPrime, Int.natCast_dvd.mp (Int.modEq_iff_dvd.mp hmod.symm)⟩

/-- Only finitely many natural primes fail to distinguish two distinct integers. -/
theorem indistinguishing_primes_finite (n m : Int) (hne : n ≠ m) :
    Set.Finite {p : Nat | Nat.Prime p ∧ Int.ModEq (p : Int) n m} := by
  refine (n - m).natAbs.primeFactors.finite_toSet.subset ?_
  intro p hp
  exact (mem_primeFactors_iff_indistinguishing n m hne p).mpr hp

#print axioms indistinguishing_primes_finite

/-- At the concrete equal pair `0, 0`, existence fails and every prime is
indistinguishing, so distinctness is necessary for both affected conclusions. -/
theorem distinctness_hypothesis_is_necessary :
    (¬ ∃ p : Nat, Nat.Prime p ∧ ¬ Int.ModEq (p : Int) 0 0) ∧
      Set.Infinite {p : Nat | Nat.Prime p ∧ Int.ModEq (p : Int) 0 0} := by
  constructor
  · simp
  · simpa using Nat.infinite_setOf_prime

#print axioms distinctness_hypothesis_is_necessary

/-- Modulus two divides `4 - 0` and does not distinguish four from zero, so the
nondivisibility premise in the separation theorem cannot be removed. -/
theorem nondivisibility_hypothesis_is_necessary :
    (2 : Int) ∣ 4 - 0 ∧ Int.ModEq 2 4 0 := by
  norm_num [Int.ModEq]

#print axioms nondivisibility_hypothesis_is_necessary

/-- Modulus two neither divides `1 - 0` nor identifies one with zero, so the
divisibility premise in the nonseparation theorem cannot be removed. -/
theorem divisibility_hypothesis_is_necessary :
    ¬ (2 : Int) ∣ 1 - 0 ∧ ¬ Int.ModEq 2 1 0 := by
  norm_num [Int.ModEq]

#print axioms divisibility_hypothesis_is_necessary

section DegenerateAudit

-- For equal inputs the nondivisibility implication is true only vacuously.
example (p : Nat) :
    ¬ (p : Int) ∣ 5 - 5 → ¬ Int.ModEq (p : Int) 5 5 := by
  exact nondividing_modulus_separates p 5 5

-- Every modulus divides the zero difference and therefore identifies equal inputs.
example (p : Nat) : Int.ModEq (p : Int) 5 5 := by
  apply dividing_modulus_does_not_separate
  simp

-- Zero is a valid endpoint: zero and one still have a distinguishing prime.
example : ∃ p : Nat, Nat.Prime p ∧ ¬ Int.ModEq (p : Int) 0 1 := by
  exact distinct_integers_have_distinguishing_prime 0 1 (by norm_num)

-- An absolute difference of one has no indistinguishing prime.
example : {p : Nat | Nat.Prime p ∧ Int.ModEq (p : Int) 0 1} = ∅ := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rw [← mem_primeFactors_iff_indistinguishing 0 1 (by norm_num)]
  simp

-- The prime-power difference eight has exactly its base prime as an exception.
example : {p : Nat | Nat.Prime p ∧ Int.ModEq (p : Int) 8 0} = {2} := by
  ext p
  rw [Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [← mem_primeFactors_iff_indistinguishing 8 0 (by norm_num)]
  change p ∈ (8 : Nat).primeFactors ↔ p = 2
  rw [show (8 : Nat).primeFactors = {2} by native_decide]
  simp

/- Empty and singleton types and constant, identity, and zero maps are inapplicable:
the declarations quantify only over integers and moduli and contain no type or map parameter. -/

end DegenerateAudit

end D5.S3.Factorization.PrimePowers.NoiselessPrimeSeparation

/- GID: D5/S3/Arith/BlindPrimes/IntegerPairClassification
   generality: G
   mirror-B: D5/B/S3/Arith/BlindPrimes/IntegerPairClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Integer residues agree at prime divisors; blind sets are finite and audited. -/

import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.Divisors

/- Library-search audit trail (2026-08-29):
   * Repository declaration, operator-shape, and `Meta/Digestion` searches found no public
     theorem classifying integer blind primes by the prime divisors of a difference.
   * `FinitelyBlindPrimeIdeals` concerns `HeightOneSpectrum` and ideal divisibility, while
     `PadicPrecisionBlindSpot` classifies exponents at one fixed prime; neither covers this.
   * Pinned Mathlib supplies `Int.modEq_iff_dvd`, `Int.natCast_dvd`, `Nat.mem_divisors`,
     and `Set.Finite.preimage_embedding`, which are reused below.
   * Exact-name searches for `natDensity`, `NaturalDensity`, and `DirichletDensity` returned
     zero files. Only unrelated Schnirelmann, graph, measure, and probability densities exist.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Exact Blind-Prime Classification for Integer Pairs

This module defines integer residue observations and their blind and separating prime sets.
It proves the exact divisibility classification, finiteness of the blind set for distinct
integers, and finiteness of the complement of the separating set.

Pinned Mathlib has no usable natural-density or Dirichlet-density definition. Accordingly,
this module formalizes only cofiniteness, not the density-one clause of the source theorem.
-/

namespace D5.S3.Arith.BlindPrimes.IntegerPairClassification

/-- The integer residue observation at modulus `p`. -/
def primeResidue (p : Nat) (x : Int) : Int :=
  x % (p : Int)

/-- The prime indices whose residue observations identify `x` and `y`. -/
def blindPrimes (x y : Int) : Set Nat.Primes :=
  {p | primeResidue p.1 x = primeResidue p.1 y}

/-- The prime indices whose residue observations distinguish `x` and `y`. -/
def separatingPrimes (x y : Int) : Set Nat.Primes :=
  {p | Ne (primeResidue p.1 x) (primeResidue p.1 y)}

/-- The prime indices dividing an integer. -/
def primeDivisors (d : Int) : Set Nat.Primes :=
  {p | (p.1 : Int) ∣ d}

/-- Two integer residues agree exactly when their modulus divides the ordered difference. -/
theorem prime_residue_eq_iff_dvd_difference (p : Nat) (x y : Int) :
    primeResidue p x = primeResidue p y ↔ (p : Int) ∣ x - y := by
  change x ≡ y [ZMOD (p : Int)] ↔ (p : Int) ∣ x - y
  rw [Int.modEq_iff_dvd]
  constructor
  · intro h
    simpa only [neg_sub] using h.neg_right
  · intro h
    simpa only [neg_sub] using h.neg_right
#print axioms prime_residue_eq_iff_dvd_difference

/-- The blind primes of a pair are exactly the prime divisors of its difference. -/
theorem blind_primes_eq_primeDivisors (x y : Int) :
    blindPrimes x y = primeDivisors (x - y) := by
  ext p
  exact prime_residue_eq_iff_dvd_difference p.1 x y
#print axioms blind_primes_eq_primeDivisors

private theorem primeDivisors_finite {d : Int} (hd : Ne d 0) :
    (primeDivisors d).Finite := by
  let valEmbedding : Nat.Primes ↪ Nat :=
    ⟨fun p => p.1, Subtype.val_injective⟩
  have hpreimage :
      (valEmbedding ⁻¹' (d.natAbs.divisors : Set Nat)).Finite :=
    Set.Finite.preimage_embedding valEmbedding
      (Set.finite_mem_finset d.natAbs.divisors)
  refine hpreimage.subset ?_
  intro p hp
  change p.1 ∈ d.natAbs.divisors
  exact Nat.mem_divisors.mpr
    ⟨Int.natCast_dvd.mp hp, Int.natAbs_ne_zero.mpr hd⟩

/-- Distinct integers have only finitely many blind prime indices. -/
theorem blind_primes_finite {x y : Int} (hxy : Ne x y) :
    (blindPrimes x y).Finite := by
  rw [blind_primes_eq_primeDivisors]
  exact primeDivisors_finite (sub_ne_zero.mpr hxy)
#print axioms blind_primes_finite

/-- For distinct integers, the separating prime set has finite complement. -/
theorem separating_primes_compl_finite {x y : Int} (hxy : Ne x y) :
    (separatingPrimes x y)ᶜ.Finite := by
  have hcomplement : (separatingPrimes x y)ᶜ = blindPrimes x y := by
    ext p
    simp only [separatingPrimes, blindPrimes, Set.mem_compl_iff,
      Set.mem_setOf_eq, not_not]
  rw [hcomplement]
  exact blind_primes_finite hxy
#print axioms separating_primes_compl_finite

/-- Equal inputs show that distinctness is necessary for blind-set finiteness. -/
theorem distinctness_is_necessary_for_blind_primes_finite :
    ¬(blindPrimes 0 0).Finite := by
  simpa [blindPrimes] using
    (Set.infinite_univ : (Set.univ : Set Nat.Primes).Infinite)
#print axioms distinctness_is_necessary_for_blind_primes_finite

section DegenerateAudit

-- Differences `1` and `-1` have no blind prime.
example : blindPrimes 1 0 = ∅ := by
  ext p
  simp only [blindPrimes, Set.mem_setOf_eq, Set.mem_empty_iff_false]
  rw [prime_residue_eq_iff_dvd_difference, sub_zero, Int.natCast_dvd]
  exact iff_false_intro (by simpa using p.2.not_dvd_one)

example : blindPrimes 0 1 = ∅ := by
  ext p
  simp only [blindPrimes, Set.mem_setOf_eq, Set.mem_empty_iff_false]
  rw [prime_residue_eq_iff_dvd_difference, Int.natCast_dvd]
  exact iff_false_intro (by
    change Not (p.1 ∣ 1)
    exact p.2.not_dvd_one)

-- A prime or positive prime power has exactly its base prime as its blind set.
example (p : Nat) (hp : p.Prime) :
    blindPrimes (p : Int) 0 = {⟨p, hp⟩} := by
  ext q
  simp only [blindPrimes, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [prime_residue_eq_iff_dvd_difference, sub_zero, Int.natCast_dvd_natCast]
  constructor
  · intro hq
    apply Subtype.ext
    exact (Nat.prime_dvd_prime_iff_eq q.2 hp).mp hq
  · intro hq
    have hvalue : q.1 = p := congrArg Subtype.val hq
    rw [hvalue]

example (p k : Nat) (hp : p.Prime) (hk : 0 < k) :
    blindPrimes ((p ^ k : Nat) : Int) 0 = {⟨p, hp⟩} := by
  ext q
  simp only [blindPrimes, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [prime_residue_eq_iff_dvd_difference, sub_zero, Int.natCast_dvd_natCast]
  constructor
  · intro hq
    apply Subtype.ext
    exact (Nat.prime_dvd_prime_iff_eq q.2 hp).mp (q.2.dvd_of_dvd_pow hq)
  · intro hq
    have hvalue : q.1 = p := congrArg Subtype.val hq
    rw [hvalue]
    exact dvd_pow_self p hk.ne'

-- Modulus two is included; modulus zero is identity and modulus one is the constant zero map.
example (x y : Int) :
    primeResidue 2 x = primeResidue 2 y ↔ (2 : Int) ∣ x - y :=
  prime_residue_eq_iff_dvd_difference 2 x y

example : primeResidue 2 0 = 0 := by
  simp [primeResidue]

example (x : Int) : primeResidue 0 x = x := by
  simp [primeResidue]

example (x : Int) : primeResidue 1 x = 0 := by
  simp [primeResidue]

-- The fixed prime index is neither empty nor a singleton; carrier-type audits are inapplicable.
example : Nonempty Nat.Primes := inferInstance

example : ∃ p q : Nat.Primes, Ne p q :=
  ⟨⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩, by decide⟩

end DegenerateAudit

end D5.S3.Arith.BlindPrimes.IntegerPairClassification

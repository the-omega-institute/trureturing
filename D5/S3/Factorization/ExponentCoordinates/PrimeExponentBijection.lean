/- GID: D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection
   generality: I
   mirror-B: D5/B/S3/Factorization/ExponentCoordinates/PrimeExponentBijection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime factorization and prime-supported products are inverse, with edge cases. -/
/- Library-search audit trail (2026-08-25):
   * Repository shape search found the existing `primeExponentLanguage` and its injectivity
     theorem, plus the reusable prime-supported type `D5.S1.Digit.PrimeExponentTable`.
   * Pinned Mathlib's `Nat.factorizationEquiv` is the exact required equivalence. Its inverse
     is a `Finsupp.prod` of prime powers, and its inverse laws use the two product lemmas.
   * No repository declaration exposed that equivalence with `primeExponentLanguage` as its
     forward map and a separately named prime-power product as its inverse. -/

import D5.S1.Digit.PrimeAxisEncoding
import D5.S3.Factorization.PrimePowers.PrimeExponentLanguageComplete

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.ExponentCoordinates.PrimeExponentBijection

open D5.S1.Digit
open D5.S3.Factorization.PrimePowers.PrimeExponentLanguageComplete

/-- Reconstruct a positive natural by taking the finite product of its prime powers. -/
def primeExponentProduct (exponents : PrimeExponentTable) : ℕ+ :=
  Nat.factorizationEquiv.symm exponents

/-- Positive naturals are equivalent to finitely supported prime-exponent families. -/
def primeExponentLanguageEquiv : ℕ+ ≃ PrimeExponentTable :=
  Nat.factorizationEquiv

/-- The forward map of the equivalence is the existing prime-exponent language. -/
@[simp] theorem prime_exponent_language_equiv_apply (n : ℕ+) :
    (primeExponentLanguageEquiv n).1 = primeExponentLanguage n :=
  rfl

#print axioms prime_exponent_language_equiv_apply

/-- The named inverse is exactly the finite product of the supported prime powers. -/
@[simp] theorem prime_exponent_product_formula (exponents : PrimeExponentTable) :
    (primeExponentProduct exponents : ℕ) =
      exponents.1.prod (fun p exponent => p ^ exponent) :=
  rfl

#print axioms prime_exponent_product_formula

/-- The existing language is bijective after restricting its codomain to prime support. -/
theorem prime_exponent_language_bijection :
    Function.Bijective primeExponentLanguageEquiv := by
  refine ⟨?_, Nat.factorizationEquiv.surjective⟩
  intro m n hmn
  exact prime_exponent_language_complete.1 (congrArg Subtype.val hmn)

#print axioms prime_exponent_language_bijection

/-- Positivity is necessary: unrestricted factorization identifies zero and one. -/
theorem positivity_restriction_is_necessary :
    ¬ Function.Injective (fun n : ℕ => n.factorization) := by
  intro hinjective
  exact Nat.zero_ne_one (hinjective (by simp))

#print axioms positivity_restriction_is_necessary

/-- Prime support is necessary: no positive natural has exponent one at the composite four. -/
theorem prime_support_restriction_is_necessary :
    ¬ Function.Surjective primeExponentLanguage := by
  intro hsurjective
  obtain ⟨n, hn⟩ := hsurjective (Finsupp.single 4 1)
  have hvalue := DFunLike.congr_fun hn 4
  change (n : ℕ).factorization 4 = Finsupp.single 4 1 4 at hvalue
  rw [Nat.factorization_eq_zero_of_not_prime (n : ℕ) (by decide)] at hvalue
  simp at hvalue

#print axioms prime_support_restriction_is_necessary

-- Empty support is the readout of one and reconstructs one.
example : primeExponentLanguage (1 : ℕ+) = 0 := by
  simp [primeExponentLanguage]

example : primeExponentProduct (⟨0, by simp⟩ : PrimeExponentTable) = 1 := by
  apply Subtype.ext
  change (0 : ℕ →₀ ℕ).prod (fun p exponent => p ^ exponent) = 1
  simp

-- A prime has one singleton exponent, and a prime power has its stated exponent.
example {p : ℕ} (hp : p.Prime) :
    primeExponentLanguage ⟨p, hp.pos⟩ = Finsupp.single p 1 := by
  simpa [primeExponentLanguage] using
    (Nat.Prime.factorization_pow (p := p) (k := 1) hp)

example {p k : ℕ} (hp : p.Prime) :
    primeExponentLanguage ⟨p ^ k, Nat.pow_pos hp.pos⟩ = Finsupp.single p k := by
  simpa [primeExponentLanguage] using
    (Nat.Prime.factorization_pow (p := p) (k := k) hp)

-- The two maps reduce to the identity in both directions, including the zero exponent family.
example (n : ℕ+) : primeExponentProduct (primeExponentLanguageEquiv n) = n :=
  Nat.factorizationEquiv.symm_apply_apply n

example (exponents : PrimeExponentTable) :
    primeExponentLanguageEquiv (primeExponentProduct exponents) = exponents :=
  Nat.factorizationEquiv.apply_symm_apply exponents

end D5.S3.Factorization.ExponentCoordinates.PrimeExponentBijection

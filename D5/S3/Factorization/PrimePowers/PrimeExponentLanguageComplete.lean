/- GID: D5/S3/Factorization/PrimePowers/PrimeExponentLanguageComplete
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/PrimeExponentLanguageComplete
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: On positive naturals, the full prime-exponent language is injective by direct application of mathlib's factorization equivalence, and every readout fiber is therefore a singleton; restricting to positive naturals excludes the indistinguishable factorization readouts of zero and one. -/

import Mathlib.Data.Nat.Factorization.Defs

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'prime_exponent_language_complete' D5 Golden/Frozen/accepted`
     returned no matches.
   * Repository searches for `factorization`, `primeExponent`, `padicValNat`, fibers,
     and injectivity found related public equivalences in `PrimeAxisEncoding` and
     `FreeCommMonoid`, plus list uniqueness in `UniqueFactorization`; none states that
     every fiber of the prime-exponent readout is a singleton.
   * The same searches found only private product-factorization helpers in
     `PrimeLogIndependence`; private declarations do not provide public coverage.
   * Mathlib search found `Nat.factorizationEquiv` in
     `Mathlib.Data.Nat.Factorization.Defs` and `Nat.factorization_inj` there as well.
     The proof applies the equivalence's injectivity directly and derives the fiber
     statement by set extensionality; it does not reprove unique factorization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.PrimeExponentLanguageComplete

/-- The full language of prime exponents read from a positive natural number. -/
def primeExponentLanguage (n : ℕ+) : ℕ →₀ ℕ :=
  (n : ℕ).factorization

/-- Full prime-exponent readout separates positive naturals and leaves singleton fibers. -/
theorem prime_exponent_language_complete :
    Function.Injective primeExponentLanguage ∧
      ∀ n : ℕ+,
        {m : ℕ+ | primeExponentLanguage m = primeExponentLanguage n} = {n} := by
  have readout_injective : Function.Injective primeExponentLanguage := by
    intro m n hmn
    exact Nat.factorizationEquiv.injective (Subtype.ext hmn)
  refine ⟨readout_injective, ?_⟩
  intro n
  ext m
  exact readout_injective.eq_iff

example :
    {m : ℕ+ | primeExponentLanguage m = primeExponentLanguage (6 : ℕ+)} =
      {(6 : ℕ+)} :=
  prime_exponent_language_complete.2 6

#print axioms prime_exponent_language_complete

end D5.S3.Factorization.PrimePowers.PrimeExponentLanguageComplete

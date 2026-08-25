/- GID: D5/S3/Zeros/PrimeRefinement/FinitePrimeExtractionZeroPersistence
   generality: I
   mirror-B: D5/B/S3/Zeros/PrimeRefinement/FinitePrimeExtractionZeroPersistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A zeta zero remains zero after multiplying by any finite set of prime Euler factors. -/

import D5.S3.Weil.PrimeAddress.PrimeAddress

/- Library-search audit trail (2026-08-24):
   * Exact current-tree hit
     `PrimeAddress.finite_prime_modification_preserves_global_zero_set` is frozen and
     proves the stronger bidirectional zero-set statement for every finite prime set.
     It is applied directly below.
   * `EulerWindows.finite_euler_window_ne_zero` is the supporting frozen theorem that
     supplies the positive-real-part regularity used by that exact hit.
   * Pinned Mathlib searches for a theorem combining `riemannZeta`, a `Finset` product,
     and zero persistence found no packaged statement. Mathlib supplies the underlying
     finite-product and division identities used by the imported theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.PrimeRefinement.FinitePrimeExtractionZeroPersistence

open D5.S3.Weil.Convention
open D5.S3.Weil.EulerProduct
open D5.S3.Weil.PrimeAddress
open D5.S3.Weil.ZeroSum
open scoped BigOperators

/-- A zero in the open critical strip remains a zero after multiplication by the
local Euler denominators from any finite set of primes. The residual is constructed
in the public conclusion directly from zeta, the supplied finite set, and its factors. -/
theorem finite_prime_extraction_preserves_zeta_zero
    (rho : ℂ) (S : Finset ℕ)
    (hPrime : ∀ p ∈ S, p.Prime)
    (hLower : 0 < rho.re) (hUpper : rho.re < 1)
    (hZero : riemannZeta rho = 0) :
    riemannZeta rho * ∏ p ∈ S, (1 - (p : ℂ) ^ (-rho)) = 0 := by
  have hNontrivial : IsNontrivialZero rho := by
    refine ⟨?_, hLower, hUpper⟩
    simpa [classicalZeta] using hZero
  have hModified : finitePrimeModification S rho = 0 :=
    (finite_prime_modification_preserves_global_zero_set S hPrime rho).mp hNontrivial |>.1
  have hResidualEq :
      finitePrimeModification S rho =
        riemannZeta rho * ∏ p ∈ S, (1 - (p : ℂ) ^ (-rho)) := by
    simp only [finitePrimeModification, finiteEulerProduct, finiteEulerDenominator,
      classicalZeta]
    rw [Finset.prod_inv_distrib]
    simp
  rw [← hResidualEq]
  exact hModified

example : Nonempty ℂ := ⟨0⟩
example : ∃ S : Finset ℕ, ∀ p ∈ S, p.Prime := ⟨∅, by simp⟩
example (Z : ZeroData) :
    ∃ rho : ℂ, 0 < rho.re ∧ rho.re < 1 ∧ riemannZeta rho = 0 := by
  refine ⟨Z.zero 0, (Z.zero_isNontrivial 0).2.1, (Z.zero_isNontrivial 0).2.2, ?_⟩
  simpa [classicalZeta] using (Z.zero_isNontrivial 0).1

#print axioms finite_prime_extraction_preserves_zeta_zero

end D5.S3.Zeros.PrimeRefinement.FinitePrimeExtractionZeroPersistence

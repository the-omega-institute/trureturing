/- GID: D5/S3/Analytic/EulerGerm/GoldenGermRealAxisPositivity
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/GoldenGermRealAxisPositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden Euler germ product is a positive real number on its full convergence ray. -/

import D5.S3.Analytic.EulerGerm.GoldenGermZetaFactorization
import Mathlib.NumberTheory.LSeries.Dirichlet

/- Library-search audit trail (2026-09-03):
   * Repository searches over `D5/**/*.lean` found no theorem asserting that
     the golden germ product has zero imaginary part and positive real part on
     the full real convergence ray. The frozen theorem
     `golden_germ_zeta_factorization` supplies both the product factorization
     and strict real-axis positivity of its normalized factor.
   * The frozen convergence theorem `germLocalFactor_multipliable` supplies the
     `Multipliable` carrier for the prime product; it is checked explicitly
     below rather than treating the total `tprod` notation as convergence.
   * Pinned Mathlib supplies `riemannZeta_re_pos_of_one_lt` and
     `riemannZeta_im_eq_zero_of_one_lt`. They state exactly that zeta is a
     positive real number at real arguments greater than one, so no Dirichlet
     series positivity argument is repeated here.

   This result concerns only the real ray inside the product's convergence
   half-plane. It does not assert a complex zero-free region and gives no O-5
   or Riemann-hypothesis conclusion. -/

namespace D5.S3.Analytic.EulerGerm.GoldenGermRealAxisPositivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.EulerGerm.GermProductConvergence
open D5.S3.Analytic.EulerGerm.GoldenGermZetaFactorization
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor

noncomputable section

/-- On every real point of the full convergence ray, the golden Euler germ
prime product is a strictly positive real number. -/
theorem golden_germ_real_axis_positivity (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 2 < sigma) :
    (∏' p : Nat.Primes, germLocalFactor (sigma : Complex) p).im = 0 ∧
      0 < (∏' p : Nat.Primes, germLocalFactor (sigma : Complex) p).re := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  have hcarrier :
      Multipliable (fun p : Nat.Primes =>
        germLocalFactor (sigma : Complex) p) :=
    germLocalFactor_multipliable (sigma : Complex) (by simpa using hsigma)
  have hhasProd : HasProd
      (fun p : Nat.Primes => germLocalFactor (sigma : Complex) p)
      (∏' p : Nat.Primes, germLocalFactor (sigma : Complex) p) :=
    hcarrier.hasProd
  rcases golden_germ_zeta_factorization with
    ⟨hfactorization, _, hnormalizedPositive⟩
  have hphiSquared : 0 < Real.goldenRatio ^ 2 :=
    sq_pos_of_pos Real.goldenRatio_pos
  have hzetaDomain : 1 < Real.goldenRatio ^ 2 * sigma := by
    have hcleared := (div_lt_iff₀ hphiSquared).mp hsigma
    nlinarith
  have hphiSquaredLtCubed :
      Real.goldenRatio ^ 2 < Real.goldenRatio ^ 3 := by
    calc
      Real.goldenRatio ^ 2 <
          Real.goldenRatio ^ 2 * Real.goldenRatio :=
        (lt_mul_iff_one_lt_right hphiSquared).mpr
          Real.one_lt_goldenRatio
      _ = Real.goldenRatio ^ 3 := by ring
  have hnormalizedDomain :
      1 / Real.goldenRatio ^ 3 < sigma :=
    (one_div_lt_one_div_of_lt hphiSquared hphiSquaredLtCubed).trans hsigma
  have hfactor := hfactorization (sigma : Complex) (by simpa using hsigma)
  have hfactoredHasProd := hhasProd
  rw [hfactor] at hfactoredHasProd
  have hfactorFromCarrier := hhasProd.unique hfactoredHasProd
  have hnormalized := hnormalizedPositive sigma hnormalizedDomain
  have hzetaRe :
      0 < (riemannZeta
        (((Real.goldenRatio ^ 2 : Real) : Complex) *
          (sigma : Complex))).re := by
    simpa only [Complex.ofReal_mul] using
      (riemannZeta_re_pos_of_one_lt hzetaDomain)
  have hzetaIm :
      (riemannZeta
        (((Real.goldenRatio ^ 2 : Real) : Complex) *
          (sigma : Complex))).im = 0 := by
    simpa only [Complex.ofReal_mul] using
      (riemannZeta_im_eq_zero_of_one_lt hzetaDomain)
  constructor
  · rw [hfactorFromCarrier, Complex.mul_im, hzetaIm, hnormalized.2]
    ring
  · rw [hfactorFromCarrier, Complex.mul_re, hzetaIm, hnormalized.2]
    simpa using mul_pos hzetaRe hnormalized.1

private theorem one_in_golden_convergence_ray :
    1 / Real.goldenRatio ^ 2 < (1 : Real) := by
  rw [div_lt_one hphiSquared]
  nlinarith [Real.one_lt_goldenRatio]
  where
    hphiSquared : 0 < Real.goldenRatio ^ 2 :=
      sq_pos_of_pos Real.goldenRatio_pos

private theorem golden_germ_real_axis_positivity_at_one :
    (∏' p : Nat.Primes, germLocalFactor (1 : Complex) p).im = 0 ∧
      0 < (∏' p : Nat.Primes, germLocalFactor (1 : Complex) p).re :=
  golden_germ_real_axis_positivity 1 one_in_golden_convergence_ray

#print axioms golden_germ_real_axis_positivity

end

end D5.S3.Analytic.EulerGerm.GoldenGermRealAxisPositivity

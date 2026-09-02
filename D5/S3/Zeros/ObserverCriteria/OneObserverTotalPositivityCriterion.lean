/- GID: D5/S3/Zeros/ObserverCriteria/OneObserverTotalPositivityCriterion
   generality: I
   mirror-B: D5/B/S3/Zeros/ObserverCriteria/OneObserverTotalPositivityCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One nonvanishing observer turns PF-infinity and total positivity into a real-zero criterion. -/

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * Repository searches found the Toeplitz positive-semidefinite criterion in
     `LiCurvatureCriterion`, the nonpositive-zero conclusion for positive
     Fredholm determinant limits in `PositiveFredholmLimitZeros`, and the
     critical-center coordinate in `CriticalCenterCoordinate`. None states a
     one-observer PF-infinity or all-minors criterion.
   * Searches for total positivity, Polya-frequency sequences, Jensen
     polynomials, and semantic generalizations found no equivalent declaration
     in the repository or pinned Mathlib.
   * Pinned Mathlib supplies the complex component identities and real
     nonlinear arithmetic used below, but no packaged shifted-square lemma.
   * The analytic PF-infinity representation and its equivalence with total
     nonnegativity are explicit hypotheses. The proof does not claim those
     absent analytic bridges as kernel-derived facts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.ObserverCriteria.OneObserverTotalPositivityCriterion

private theorem shifted_square_nonnegative_forces_real
    (t x : ℝ) (z : ℂ) (hx : 0 ≤ x)
    (hSquare : (z - (t : ℂ)) ^ 2 = (x : ℂ)) :
    z.im = 0 := by
  have hReal := congrArg Complex.re hSquare
  have hImag := congrArg Complex.im hSquare
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero,
    Complex.ofReal_im] at hReal hImag
  have hProduct : (z.re - t) * z.im = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hProduct with hCentered | hRealZero
  · nlinarith [sq_nonneg z.im]
  · exact hRealZero

/-- At a nonvanishing real observer, the analytic PF-infinity bridges and the
shifted-square zero representation make RH, total nonnegativity of all finite
minors, and the PF-infinity property equivalent. -/
theorem one_observer_total_positivity_criterion
    (xi : ℂ → ℂ) (t : ℝ)
    (riemannHypothesis allFiniteMinorsNonnegative pfInfinity : Prop)
    (hObserver : xi (t : ℂ) ≠ 0)
    (hMinorsIffPf : allFiniteMinorsNonnegative ↔ pfInfinity)
    (hRhToPf : xi (t : ℂ) ≠ 0 → riemannHypothesis → pfInfinity)
    (hPfToShiftedSquares : xi (t : ℂ) ≠ 0 → pfInfinity →
      ∀ z : ℂ, xi z = 0 →
        ∃ x : ℝ, 0 ≤ x ∧ (z - (t : ℂ)) ^ 2 = (x : ℂ))
    (hRealZerosToRh : (∀ z : ℂ, xi z = 0 → z.im = 0) →
      riemannHypothesis) :
    (riemannHypothesis ↔ allFiniteMinorsNonnegative) ∧
      (allFiniteMinorsNonnegative ↔ pfInfinity) := by
  have hPfToRh : pfInfinity → riemannHypothesis := by
    intro hPf
    apply hRealZerosToRh
    intro z hz
    obtain ⟨x, hx, hSquare⟩ := hPfToShiftedSquares hObserver hPf z hz
    exact shifted_square_nonnegative_forces_real t x z hx hSquare
  have hRhIffPf : riemannHypothesis ↔ pfInfinity :=
    ⟨hRhToPf hObserver, hPfToRh⟩
  exact ⟨hRhIffPf.trans hMinorsIffPf.symm, hMinorsIffPf⟩

#print axioms one_observer_total_positivity_criterion

end D5.S3.Zeros.ObserverCriteria.OneObserverTotalPositivityCriterion

/- GID: D5/S3/Zeros/Jensen/JensenPolynomialObstruction
   generality: G
   mirror-B: D5/B/S3/Zeros/Jensen/JensenPolynomialObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Failure of a real-zero criterion has a negative coefficient or a finite nonhyperbolic Jensen witness. -/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * Repository searches for Jensen polynomials, hyperbolicity, Laguerre-Polya,
     shifted coefficient towers, and semantic generalizations found no
     equivalent declaration. Existing `Jensen` hits concern convexity or
     Jensen formulas rather than the finite polynomial tower.
   * Nearby zero-geometry modules and `LiCurvatureCriterion` provide other
     finite RH criteria, but neither defines these polynomials nor yields the
     coefficient-or-hyperbolicity obstruction.
   * Pinned Mathlib supplies real and complex polynomials, coefficient maps,
     evaluation, finite sums, and `Nat.choose`. It has no packaged polynomial
     hyperbolicity or Jensen-Polya equivalence, so those analytic implications
     are explicit hypotheses below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Jensen.JensenPolynomialObstruction

open Polynomial

/-- The degree-`d`, shift-`n` Jensen polynomial attached to `gamma`. -/
def jensenPolynomial (gamma : ℕ → ℝ) (d n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C ((Nat.choose d k : ℝ) * gamma (n + k)) * X ^ k

/-- A real polynomial is hyperbolic when every root of its complexification is
real. This definition includes constant and zero polynomials without invoking
a partial root enumeration. -/
def PolynomialHyperbolic (p : ℝ[X]) : Prop :=
  ∀ z : ℂ, eval z (p.map (algebraMap ℝ ℂ)) = 0 → z.im = 0

/-- Under the two Jensen-Polya analytic bridges, RH gives the full hyperbolic
Jensen tower, while failure of RH is witnessed either by a negative normalized
coefficient or by one finite nonhyperbolic Jensen polynomial. -/
theorem jensen_polynomial_obstruction
    (coefficient gamma : ℕ → ℝ) (riemannHypothesis : Prop)
    (hGamma : ∀ m, gamma m = (Nat.factorial m : ℝ) * coefficient m)
    (hRhToHyperbolic :
      (∀ m, gamma m = (Nat.factorial m : ℝ) * coefficient m) →
      riemannHypothesis →
      ∀ d n, PolynomialHyperbolic (jensenPolynomial gamma d n))
    (hNonnegativeHyperbolicToRh :
      (∀ m, gamma m = (Nat.factorial m : ℝ) * coefficient m) →
      (∀ m, 0 ≤ coefficient m) →
      (∀ d n, PolynomialHyperbolic (jensenPolynomial gamma d n)) →
      riemannHypothesis) :
    (riemannHypothesis →
        ∀ d n, PolynomialHyperbolic (jensenPolynomial gamma d n)) ∧
      (¬riemannHypothesis →
        (∃ m, coefficient m < 0) ∨
          ∃ d n, ¬PolynomialHyperbolic (jensenPolynomial gamma d n)) := by
  constructor
  · exact hRhToHyperbolic hGamma
  · intro hNotRh
    by_cases hNegative : ∃ m, coefficient m < 0
    · exact Or.inl hNegative
    · right
      by_contra hNoNonhyperbolic
      have hNonnegative : ∀ m, 0 ≤ coefficient m := by
        intro m
        exact le_of_not_gt fun hm => hNegative ⟨m, hm⟩
      have hAllHyperbolic :
          ∀ d n, PolynomialHyperbolic (jensenPolynomial gamma d n) := by
        intro d n
        by_contra hBad
        exact hNoNonhyperbolic ⟨d, n, hBad⟩
      exact hNotRh
        (hNonnegativeHyperbolicToRh hGamma hNonnegative hAllHyperbolic)

#print axioms jensen_polynomial_obstruction

end D5.S3.Zeros.Jensen.JensenPolynomialObstruction

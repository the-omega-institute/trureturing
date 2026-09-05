/- GID: D5/S3/Weil/ChebyshevOffLineStrictNegativity
   generality: G
   mirror-B: D5/B/S3/Weil/ChebyshevOffLineStrictNegativity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive Chebyshev degrees give strict off-line negativity. -/

import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Artanh
import D5.S3.Weil.CayleyLaguerre.ChebyshevSlackPositivity
import Mathlib.Tactic

/-!
# Chebyshev off-line strict negativity

The rational compactification of a negative squared distance lies below `-1`.
Its hyperbolic rapidity converts every positive Chebyshev degree into an exact
negative squared-sinh slack.  The hypotheses exclude the two genuine equality
cases: zero transverse distance and zero Chebyshev degree.

Library-search audit trail (2026-09-03):

* Literal, notation-variant, receipt, digest, generalized-owner, and in-flight
  branch searches found no theorem giving the general-degree hyperbolic identity.
* `ChebyshevSlackPositivity` proves the on-line interval bound, while
  `ChebyshevSignedDistanceSeparator` and `ChebyshevSignedDistanceMargin` cover
  only degree one.
* Mathlib's `Polynomial.Chebyshev.T_eval_neg` and `T_real_cosh` give the exact
  polynomial step.  `Real.cosh_arcosh`, `Real.arcosh_cosh`,
  `Real.cosh_artanh`, and `Real.sinh_artanh` supply the rapidity conversion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ChebyshevOffLineStrictNegativity

/-- Rational coordinate used to compactify a squared spectral parameter. -/
def compactCoordinate (a x : Real) : Real :=
  (x - a) / (x + a)

/-- Hyperbolic rapidity of a transverse distance below the compactification pole. -/
def transverseRapidity (a delta : Real) : Real :=
  Real.arcosh ((a + delta ^ 2) / (a - delta ^ 2))

/-- First-kind Chebyshev slack at a compactified spectral parameter. -/
def chebyshevSlack (N : Nat) (a x : Real) : Real :=
  1 - (Polynomial.Chebyshev.T Real (N : Int)).eval (compactCoordinate a x) ^ 2

/-- For positive scale, nonzero transverse distance below the pole, and positive
degree, the off-line slack is exactly a negative squared hyperbolic sine.  The
same compactification sends every nonnegative input to nonnegative slack. -/
theorem chebyshev_off_line_strict_negativity
    (N : Nat) (a x delta : Real)
    (hN : 0 < N) (ha : 0 < a) (hx : 0 <= x)
    (hdelta : delta ≠ 0) (hscale : delta ^ 2 < a) :
    let kappa := transverseRapidity a delta
    compactCoordinate a (-delta ^ 2) = -Real.cosh kappa /\
      kappa = 2 * Real.artanh (|delta| / Real.sqrt a) /\
      (Polynomial.Chebyshev.T Real (N : Int)).eval
          (compactCoordinate a (-delta ^ 2)) =
        (-1 : Real) ^ N * Real.cosh ((N : Real) * kappa) /\
      chebyshevSlack N a (-delta ^ 2) =
        -Real.sinh ((N : Real) * kappa) ^ 2 /\
      chebyshevSlack N a (-delta ^ 2) < 0 /\
      compactCoordinate a x ∈ Set.Icc (-1) 1 /\
      chebyshevSlack N a x ∈ Set.Icc 0 1 := by
  dsimp only
  have hsqrtPositive : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsqrtSquare : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  let ratio : Real := |delta| / Real.sqrt a
  have habsDeltaPositive : 0 < |delta| := abs_pos.mpr hdelta
  have hratioPositive : 0 < ratio := div_pos habsDeltaPositive hsqrtPositive
  have habsDeltaLtSqrt : |delta| < Real.sqrt a := by
    nlinarith [sq_abs delta, hsqrtSquare]
  have hratioLtOne : ratio < 1 :=
    (div_lt_one hsqrtPositive).2 habsDeltaLtSqrt
  have hratio : ratio ∈ Set.Ioo (-1 : Real) 1 := by
    exact ⟨by linarith, hratioLtOne⟩
  have hCoshTwoArtanh (r : Real) (hr : r ∈ Set.Ioo (-1 : Real) 1) :
      Real.cosh (2 * Real.artanh r) = (1 + r ^ 2) / (1 - r ^ 2) := by
    have hOneMinusSquare : 0 <= 1 - r ^ 2 := by
      nlinarith [hr.1, hr.2]
    rw [Real.cosh_two_mul, Real.cosh_artanh hr,
      Real.sinh_artanh hr, div_pow, one_pow, div_pow,
      Real.sq_sqrt hOneMinusSquare]
    ring
  have hCoshDouble :
      Real.cosh (2 * Real.artanh ratio) =
        (1 + ratio ^ 2) / (1 - ratio ^ 2) :=
    hCoshTwoArtanh ratio hratio
  have hRatioSquare : ratio ^ 2 = delta ^ 2 / a := by
    dsimp only [ratio]
    rw [div_pow, sq_abs, hsqrtSquare]
  have hDenominatorPositive : 0 < a - delta ^ 2 := sub_pos.mpr hscale
  have hCoshRatio :
      Real.cosh (2 * Real.artanh ratio) =
        (a + delta ^ 2) / (a - delta ^ 2) := by
    rw [hCoshDouble, hRatioSquare]
    field_simp [ha.ne', hDenominatorPositive.ne']
  have hHyperbolicRatio : 1 < (a + delta ^ 2) / (a - delta ^ 2) := by
    rw [lt_div_iff₀ hDenominatorPositive]
    nlinarith [sq_pos_of_ne_zero hdelta]
  have hRapidityArtanh :
      transverseRapidity a delta = 2 * Real.artanh ratio := by
    rw [transverseRapidity, ← hCoshRatio]
    exact Real.arcosh_cosh (mul_nonneg (by norm_num)
      (Real.artanh_nonneg hratioPositive.le))
  have hRapidityPositive : 0 < transverseRapidity a delta := by
    exact Real.arcosh_pos hHyperbolicRatio
  have hOffCoordinate :
      compactCoordinate a (-delta ^ 2) =
        -Real.cosh (transverseRapidity a delta) := by
    rw [compactCoordinate, transverseRapidity,
      Real.cosh_arcosh hHyperbolicRatio.le]
    rw [show -delta ^ 2 + a = a - delta ^ 2 by ring,
      show -delta ^ 2 - a = -(a + delta ^ 2) by ring, neg_div]
  have hChebyshev :
      (Polynomial.Chebyshev.T Real (N : Int)).eval
          (compactCoordinate a (-delta ^ 2)) =
        (-1 : Real) ^ N *
          Real.cosh ((N : Real) * transverseRapidity a delta) := by
    rw [hOffCoordinate, Polynomial.Chebyshev.T_eval_neg,
      Polynomial.Chebyshev.T_real_cosh]
    simp only [Int.cast_natCast, Int.cast_negOnePow_natCast]
  have hSlackIdentity :
      chebyshevSlack N a (-delta ^ 2) =
        -Real.sinh ((N : Real) * transverseRapidity a delta) ^ 2 := by
    rw [chebyshevSlack, hChebyshev]
    have hSignSquare : ((-1 : Real) ^ N) ^ 2 = 1 := by
      rw [← pow_mul]
      simp
    rw [mul_pow, hSignSquare, one_mul]
    nlinarith [Real.cosh_sq_sub_sinh_sq
      ((N : Real) * transverseRapidity a delta)]
  have hArgumentPositive :
      0 < (N : Real) * transverseRapidity a delta := by
    exact mul_pos (Nat.cast_pos.mpr hN) hRapidityPositive
  have hSlackNegative : chebyshevSlack N a (-delta ^ 2) < 0 := by
    rw [hSlackIdentity]
    exact neg_lt_zero.mpr (sq_pos_of_pos (Real.sinh_pos_iff.mpr hArgumentPositive))
  have hScaledCoordinate :
      (x / a - 1) / (x / a + 1) = compactCoordinate a x := by
    rw [compactCoordinate]
    field_simp [ha.ne']
  have hOn :=
    D5.S3.Weil.CayleyLaguerre.ChebyshevSlackPositivity.chebyshev_slack_bounds
      N 1 (x / a) (by norm_num) (div_nonneg hx ha.le)
  dsimp only at hOn
  rw [hScaledCoordinate] at hOn
  have hOnCoordinate : compactCoordinate a x ∈ Set.Icc (-1 : Real) 1 := hOn.1
  have hOnSlack : chebyshevSlack N a x ∈ Set.Icc (0 : Real) 1 := by
    simpa only [chebyshevSlack] using hOn.2
  refine ⟨hOffCoordinate, ?_, hChebyshev, hSlackIdentity, hSlackNegative,
    hOnCoordinate, hOnSlack⟩
  simpa only [ratio] using hRapidityArtanh

/-- The excluded zero-degree and zero-distance cases attain equality, so the
strictness assumptions in `chebyshev_off_line_strict_negativity` are necessary. -/
theorem chebyshev_off_line_degenerate_equalities (a : Real) (ha : 0 < a) :
    chebyshevSlack 0 a (-1) = 0 /\
      chebyshevSlack 1 a (-(0 : Real) ^ 2) = 0 := by
  constructor
  · simp [chebyshevSlack]
  · simp [chebyshevSlack, compactCoordinate, ha.ne']

#print axioms chebyshev_off_line_strict_negativity
#print axioms chebyshev_off_line_degenerate_equalities

end D5.S3.Weil.ChebyshevOffLineStrictNegativity

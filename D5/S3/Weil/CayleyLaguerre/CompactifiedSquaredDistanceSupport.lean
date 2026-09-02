/- GID: D5/S3/Weil/CayleyLaguerre/CompactifiedSquaredDistanceSupport
   generality: G
   mirror-B: D5/B/S3/Weil/CayleyLaguerre/CompactifiedSquaredDistanceSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compactified squared distances characterize RH support. -/

import D5.S3.Weil.CayleyLaguerre.ChebyshevSignedDistanceSeparator
import D5.S3.Weil.ZetaCore.Statement
import Mathlib.Tactic

/-!
# Compactified squared-distance support

The rational compactification `(x - a) / (x + a)` sends every nonnegative
squared distance into `[-1, 1)`. At the signed distance `-delta^2`, the source
strip bound keeps the denominator positive and the coordinate lies below
`-1` with the stated exact value.

For a zeta zero `rho`, observing at its ordinate constructs the signed squared
distance `-(rho.re - 1/2)^2`. Requiring the rational coordinate to be defined
and lie in `[-1, 1]` for every Mathlib-nontrivial zero is equivalent to
Mathlib's `RiemannHypothesis`: a nonzero horizontal displacement maps outside
the interval on either side of the compactification pole.

Library-search audit trail (2026-09-03):

* Body-shape searches for `(x - a) / (x + a)` found the frozen canonical
  compactification in `ChebyshevSlackPositivity` and its signed extension in
  `ChebyshevSignedDistanceSeparator`; the latter is imported and applied.
* Searches for `RiemannHypothesis`, strip zeros, and support criteria found
  `Zeta23.RH_implies_on_line`, but no existing D5 theorem states the reverse
  support implication or the complete three-clause result below.
* Pinned Mathlib defines `RiemannHypothesis` over `riemannZeta` zeros and
  supplies no theorem for this project-specific compactified support
  criterion. Installed third-party packages expose no matching declaration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.CayleyLaguerre.CompactifiedSquaredDistanceSupport

open D5.S3.Weil.CayleyLaguerre.ChebyshevSignedDistanceSeparator

/-- A concrete witness that the source hypotheses are jointly satisfiable. -/
example :
    ∃ a x delta : Real,
      (1 : Real) / 4 < a ∧
        0 <= x ∧
        0 < |delta| ∧
        delta ^ 2 < (1 : Real) / 4 := by
  refine ⟨1, 0, (1 : Real) / 4, ?_⟩
  norm_num

/-- Above the source scale threshold, the Cayley compactification places a
nonnegative squared distance in `[-1, 1)`, places every genuine target
distance `-delta^2` from the critical strip below `-1`, and turns RH into the
support condition for the signed squared distances observed at zero ordinates.

The nonzero-denominator conjunct makes explicit the ordinary mathematical
domain of the rational compactification; Lean's totalized division would
otherwise assign the pole the spurious value zero. -/
theorem compactified_squared_distance_support_criterion
    (a x delta : Real)
    (ha : (1 : Real) / 4 < a)
    (hx : 0 <= x)
    (hdelta : 0 < |delta|)
    (hdeltaStrip : delta ^ 2 < (1 : Real) / 4) :
    let compactCoordinate := fun y : Real => (y - a) / (y + a)
    (-1 <= compactCoordinate x ∧ compactCoordinate x < 1) ∧
      (compactCoordinate (-delta ^ 2) =
          -(a + delta ^ 2) / (a - delta ^ 2) ∧
        compactCoordinate (-delta ^ 2) < -1) ∧
      (RiemannHypothesis ↔
        ∀ rho : Complex,
          riemannZeta rho = 0 →
          (¬∃ n : Nat, rho = -2 * (n + 1)) →
          rho ≠ 1 →
          let signedSquaredDistance := -(rho.re - (1 : Real) / 2) ^ 2
          signedSquaredDistance + a ≠ 0 ∧
            compactCoordinate signedSquaredDistance ∈ Set.Icc (-1) 1) := by
  dsimp only
  have haPositive : 0 < a := by
    linarith
  have hScale : delta ^ 2 < a := by
    linarith
  have hAbsScale : |delta| ^ 2 < a := by
    simpa only [sq_abs] using hScale
  have hSeparator :=
    first_chebyshev_slack_separates_signed_squared_distance
      a x |delta| ha hx hdelta hAbsScale
  dsimp only at hSeparator
  have hDenominator : 0 < x + a := by
    linarith
  refine ⟨⟨hSeparator.1.1, ?_⟩, ?_, ?_⟩
  · rw [div_lt_iff₀ hDenominator]
    linarith
  · constructor
    · rw [show -delta ^ 2 + a = a - delta ^ 2 by ring]
      rw [show -delta ^ 2 - a = -(a + delta ^ 2) by ring]
    · simpa only [sq_abs] using hSeparator.2.2.1
  · constructor
    · intro hRH rho hzero hnotTrivial hone
      have hline : rho.re = (1 : Real) / 2 :=
        hRH rho hzero hnotTrivial hone
      rw [hline]
      have haNe : a ≠ 0 := ne_of_gt haPositive
      simp [haNe]
    · intro hSupport rho hzero hnotTrivial hone
      have hAtRho := hSupport rho hzero hnotTrivial hone
      rcases hAtRho with ⟨hAwayFromPole, hLower, hUpper⟩
      by_contra hOffLine
      have hSquarePositive :
          0 < (rho.re - (1 : Real) / 2) ^ 2 :=
        sq_pos_of_ne_zero (sub_ne_zero.mpr hOffLine)
      by_cases hBelowPole : (rho.re - (1 : Real) / 2) ^ 2 < a
      · have hPositiveDenominator :
            0 < -(rho.re - (1 : Real) / 2) ^ 2 + a := by
          linarith
        have hBelowInterval :
            (-(rho.re - (1 : Real) / 2) ^ 2 - a) /
                (-(rho.re - (1 : Real) / 2) ^ 2 + a) < -1 := by
          rw [div_lt_iff₀ hPositiveDenominator]
          nlinarith
        exact (not_lt_of_ge hLower) hBelowInterval
      · have hSquareNeScale :
            (rho.re - (1 : Real) / 2) ^ 2 ≠ a := by
          intro hEqual
          apply hAwayFromPole
          rw [hEqual]
          ring
        have hAbovePole : a < (rho.re - (1 : Real) / 2) ^ 2 := by
          exact lt_of_le_of_ne (le_of_not_gt hBelowPole) hSquareNeScale.symm
        have hNegativeDenominator :
            -(rho.re - (1 : Real) / 2) ^ 2 + a < 0 := by
          linarith
        have hAboveInterval :
            1 < (-(rho.re - (1 : Real) / 2) ^ 2 - a) /
                (-(rho.re - (1 : Real) / 2) ^ 2 + a) := by
          rw [lt_div_iff_of_neg hNegativeDenominator]
          nlinarith
        exact (not_lt_of_ge hUpper) hAboveInterval

#print axioms compactified_squared_distance_support_criterion

end D5.S3.Weil.CayleyLaguerre.CompactifiedSquaredDistanceSupport

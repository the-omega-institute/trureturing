/- GID: D5/S3/Weil/CayleyLaguerre/ChebyshevSignedDistanceMargin
   generality: G
   mirror-B: D5/B/S3/Weil/CayleyLaguerre/ChebyshevSignedDistanceMargin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The first off-line Chebyshev slack has an exact positive separation margin. -/

import D5.S3.Weil.CayleyLaguerre.ChebyshevSignedDistanceSeparator
import Mathlib.Tactic

/-!
# Chebyshev signed-distance margin

The signed-distance separator has an exact quantitative margin. For the
negative support point `-delta^2`, the first Chebyshev slack is the negative of

`4 * a * delta^2 / (a - delta^2)^2`.

The denominator condition `delta^2 < a` places the observation below the
compactification pole and makes this margin strictly positive. The theorem
only computes the finite algebraic margin. It does not supply spectral
isolation, a tail bound, or an RH conclusion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.CayleyLaguerre.ChebyshevSignedDistanceMargin

/-- The first Chebyshev slack at the negative signed squared distance
`-delta^2` equals the negative of an explicit strictly positive margin. -/
theorem first_chebyshev_off_line_exact_margin
    (a delta : Real)
    (hdelta : 0 < delta)
    (hscale : delta ^ 2 < a) :
    let offLineCoordinate := (-delta ^ 2 - a) / (-delta ^ 2 + a)
    let offLineSlack := 1 -
      (Polynomial.Chebyshev.T Real (1 : Int)).eval offLineCoordinate ^ 2
    let margin := 4 * a * delta ^ 2 / (a - delta ^ 2) ^ 2
    offLineSlack = -margin /\ 0 < margin := by
  dsimp only
  have hDeltaSquare : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have ha : 0 < a := by
    linarith
  have hDenominator : a - delta ^ 2 ≠ 0 :=
    ne_of_gt (sub_pos.mpr hscale)
  have hDenominator' : -delta ^ 2 + a ≠ 0 := by
    linarith
  have hDenominatorSquare : 0 < (a - delta ^ 2) ^ 2 :=
    sq_pos_of_ne_zero hDenominator
  have hChebyshevOne :
      (Polynomial.Chebyshev.T Real (1 : Int)).eval
          ((-delta ^ 2 - a) / (-delta ^ 2 + a)) =
        (-delta ^ 2 - a) / (-delta ^ 2 + a) := by
    simp
  rw [hChebyshevOne]
  constructor
  · field_simp [hDenominator, hDenominator']
    ring
  · exact div_pos (by positivity) hDenominatorSquare

#print axioms first_chebyshev_off_line_exact_margin

end D5.S3.Weil.CayleyLaguerre.ChebyshevSignedDistanceMargin

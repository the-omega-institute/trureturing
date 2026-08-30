/- GID: D5/S3/Weil/CayleyLaguerre/ChebyshevSignedDistanceSeparator
   generality: G
   mirror-B: D5/B/S3/Weil/CayleyLaguerre/ChebyshevSignedDistanceSeparator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: First Chebyshev slack separates nonnegative and negative squared distances. -/

import D5.S3.Weil.CayleyLaguerre.ChebyshevSlackPositivity
import Mathlib.Tactic

/-!
# Chebyshev signed-distance separator

The compact coordinate used by `ChebyshevSlackPositivity` has a strict
one-step extension across the nonnegative squared-distance boundary.
Nonnegative squared distances give slack in `[0, 1]`; a genuine negative
signed squared distance `-delta^2`, observed below the compactification pole,
gives a coordinate below `-1` and strictly negative first Chebyshev slack.

This theorem is only the algebraic separator. It does not assume that a
specific spectral problem supplies such a signed-distance observation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.CayleyLaguerre.ChebyshevSignedDistanceSeparator

/-- At any scale above one quarter, the first Chebyshev slack separates every
nonnegative squared distance from the negative signed value `-delta^2`,
provided the scale lies above `delta^2`. -/
theorem first_chebyshev_slack_separates_signed_squared_distance
    (a x delta : Real)
    (ha : (1 : Real) / 4 < a)
    (hx : 0 <= x)
    (hdelta : 0 < delta)
    (hscale : delta ^ 2 < a) :
    let onLineCoordinate := (x - a) / (x + a)
    let onLineSlack := 1 -
      (Polynomial.Chebyshev.T Real (1 : Int)).eval onLineCoordinate ^ 2
    let offLineCoordinate := (-delta ^ 2 - a) / (-delta ^ 2 + a)
    let offLineSlack := 1 -
      (Polynomial.Chebyshev.T Real (1 : Int)).eval offLineCoordinate ^ 2
    onLineCoordinate ∈ Set.Icc (-1) 1 /\
      onLineSlack ∈ Set.Icc 0 1 /\
      offLineCoordinate < -1 /\
      offLineSlack < 0 := by
  dsimp only
  have hOn :=
    D5.S3.Weil.CayleyLaguerre.ChebyshevSlackPositivity.chebyshev_slack_bounds
      1 a x ha hx
  dsimp only at hOn
  rcases hOn with ⟨hOnCoordinate, hOnSlack⟩
  have hDeltaSquare : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have hDenominator : 0 < -delta ^ 2 + a := by
    linarith
  have hOffCoordinate :
      (-delta ^ 2 - a) / (-delta ^ 2 + a) < (-1 : Real) := by
    rw [div_lt_iff₀ hDenominator]
    nlinarith
  have hChebyshevOne :
      (Polynomial.Chebyshev.T Real (1 : Int)).eval
          ((-delta ^ 2 - a) / (-delta ^ 2 + a)) =
        (-delta ^ 2 - a) / (-delta ^ 2 + a) := by
    simp
  have hOffSlack :
      1 -
          (Polynomial.Chebyshev.T Real (1 : Int)).eval
              ((-delta ^ 2 - a) / (-delta ^ 2 + a)) ^ 2 <
        0 := by
    rw [hChebyshevOne]
    nlinarith
  exact ⟨hOnCoordinate, hOnSlack, hOffCoordinate, hOffSlack⟩

#print axioms first_chebyshev_slack_separates_signed_squared_distance

end D5.S3.Weil.CayleyLaguerre.ChebyshevSignedDistanceSeparator

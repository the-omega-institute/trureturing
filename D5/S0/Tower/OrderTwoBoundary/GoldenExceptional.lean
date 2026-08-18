/- GID: D5/S0/Tower/OrderTwoBoundary/GoldenExceptional
   generality: I
   mirror-B: D5/B/S0/Tower/OrderTwoBoundary/GoldenExceptional
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The general champion formula vanishes at order two, so it excludes gold. -/

import D5.S0.Tower.DBonacciGeneral.ChampionValue
import D5.S0.Tower.Champions.GoldenSurvivorTubes

/- Library-search audit trail (2026-08-18):
   * Repository search found `championValue`, `goldenThreshold`, and the
     order-two Perron-root identification, but no statement recording why the
     general champion formula must exclude order two.
   * Pinned Mathlib supplies `Real.goldenRatio_sq`; nothing else is needed. -/

namespace D5.S0.Tower.OrderTwoBoundary.GoldenExceptional

open D5.S0.Tower.DBonacciGeneral.ChampionValue
open D5.S0.Tower.Champions.GoldenSurvivorTubes

local notation "φ" => Real.goldenRatio

/-- The quantity that the general champion formula divides by the squared base
less one.  It is the golden minimal polynomial, so it vanishes exactly at gold. -/
theorem golden_numerator_vanishes : φ ^ 2 - φ - 1 = 0 := by
  have := Real.goldenRatio_sq
  linarith

/-- Hence the general formula returns zero at order two. -/
theorem championValue_goldenRatio : championValue φ = 0 := by
  simp only [championValue, golden_numerator_vanishes, zero_div]

/-- The order-two tower's own champion value is strictly positive. -/
theorem goldenThreshold_pos : 0 < goldenThreshold := by
  rw [golden_threshold_eq]
  have := golden_inverse_pos
  positivity

/-- Therefore the general formula does not compute the order-two champion value.
The gap is the whole of the order-two threshold, not a perturbation. -/
theorem championValue_goldenRatio_ne_goldenThreshold :
    championValue φ ≠ goldenThreshold := by
  rw [championValue_goldenRatio]
  exact ne_of_lt goldenThreshold_pos

/-- The same vanishing numerator makes the order-two case degenerate in the
finite-depth argument.  There the predecessor coordinate must stay at or below
the reciprocal base, which after clearing denominators reads `beta ≤ beta² - 1`,
that is positivity of the same numerator.  At gold it holds with equality. -/
theorem golden_reciprocal_boundary_is_tight : φ = φ ^ 2 - 1 := by
  have := Real.goldenRatio_sq
  linarith

/-- The order-two exclusion, stated as one proposition: the numerator vanishes,
the general formula returns zero, and the true order-two champion value is
strictly positive, so the two disagree. -/
theorem order_two_is_outside_the_general_formula :
    φ ^ 2 - φ - 1 = 0 ∧
      championValue φ = 0 ∧
      0 < goldenThreshold ∧
      championValue φ ≠ goldenThreshold :=
  ⟨golden_numerator_vanishes, championValue_goldenRatio, goldenThreshold_pos,
    championValue_goldenRatio_ne_goldenThreshold⟩

end D5.S0.Tower.OrderTwoBoundary.GoldenExceptional

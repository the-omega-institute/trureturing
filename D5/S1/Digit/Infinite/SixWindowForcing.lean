/- GID: D5/S1/Digit/Infinite/SixWindowForcing
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SixWindowForcing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local separation and arbitrary-length six-window forcing for actual paired sources. -/

import D5.S1.Digit.Infinite.CriticalPrefixSeparation
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace D5.S1.Digit.Infinite.SixWindowForcing

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.CriticalPrefixSeparation (residual)

/-- The finite-delay critical budget. -/
noncomputable def rho : ℝ := (239 * g - 44) / 380

/-- The three-color bounds for the two third-color choices of separation type three. -/
noncomputable def K31 : ℝ := (47 * g - 11) / 50
noncomputable def K32 : ℝ := (5 - 21 * g) / 20
/-- The three-color bound for separation type four. -/
noncomputable def K4 : ℝ := (9 * g - 2) / 25
/-- The four-color return bound for separation type two. -/
noncomputable def J : ℝ := 2 * g ^ 4 / (5 * (1 + g ^ 3))

/-- The alternating six-window source words. -/
def blockA : List Label := [threeLabel, threeLabel, fiveLabel, nullLabel, threeLabel, nullLabel]
def blockB : List Label := [nullLabel, threeLabel, nullLabel, threeLabel, threeLabel, fiveLabel]

end D5.S1.Digit.Infinite.SixWindowForcing

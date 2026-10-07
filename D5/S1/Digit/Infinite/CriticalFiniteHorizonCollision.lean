/- GID: D5/S1/Digit/Infinite/CriticalFiniteHorizonCollision
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/CriticalFiniteHorizonCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict critical collisions of actual finite sources at every finite horizon. -/

import D5.S1.Digit.Infinite.CriticalPrefixSeparation
import Mathlib.Order.Interval.Set.ProjIcc

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.CriticalFiniteHorizonCollision

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.CriticalPrefixSeparation
open D5.S1.Digit.Infinite.OddColorThreeSource (shift_add golden_relations)
open D5.S1.Scale (embedding)
open D5.S0.Carrier (GoldenInt)
open Set Filter
open scoped Topology

/-- The interior guard-one coordinate used for the first critical gap. -/
noncomputable def yStar : ℝ := (t - 4) / 5

end D5.S1.Digit.Infinite.CriticalFiniteHorizonCollision

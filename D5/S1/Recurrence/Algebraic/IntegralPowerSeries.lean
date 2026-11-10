/- GID: D5/S1/Recurrence/Algebraic/IntegralPowerSeries
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/IntegralPowerSeries
   mirror-E: none(waiver:unbounded-symbolic-mathematics)
   anchors: []
   utility: none
   digest: Integer-image coefficients over every characteristic-zero field. -/

/- The integer-image predicate has its original qualified name and exact
field/characteristic-zero telescope. Both Euler ghosts and logarithmic
transforms use this single definition. -/

import Mathlib.RingTheory.PowerSeries.Exp

open PowerSeries

namespace D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure

def IntegralSeries {K : Type*} [Field K] [CharZero K] (f : PowerSeries K) : Prop :=
  ∀ n, ∃ z : ℤ, coeff n f = (z : K)

end D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure

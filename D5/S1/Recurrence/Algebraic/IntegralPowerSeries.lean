/- GID: D5/S1/Recurrence/Algebraic/IntegralPowerSeries
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/IntegralPowerSeries
   mirror-E: none(waiver:unbounded-symbolic-mathematics)
   anchors: []
   utility: none
   digest: Integer-image coefficients over every characteristic-zero field. -/

/- This is the existing frozen integer-image predicate, moved without changing
its name or defining expression to the common dependency of Euler ghosts and
logarithmic transforms. It adds no theorem or duplicate predicate. The stable
namespace preserves all existing mathematical statements. -/

import Mathlib.RingTheory.PowerSeries.Exp

open PowerSeries

namespace D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure

def IntegralSeries {K : Type*} [Field K] [CharZero K] (f : PowerSeries K) : Prop :=
  ∀ n, ∃ z : ℤ, coeff n f = (z : K)

end D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure

/- GID: D5/S1/Dynamics/PeriodicOrbits/SkewZModOrder
   generality: G
   mirror-B: D5/B/S1/Dynamics/PeriodicOrbits/SkewZModOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite cyclic holonomy turns skew return periods into a gcd quotient. -/

import D5.S1.Dynamics.PeriodicOrbits.SkewAdditiveReturn
import Mathlib.Data.ZMod.Basic

/-! # Finite cyclic holonomy -/

set_option autoImplicit false

namespace D5.S1.Dynamics.PeriodicOrbits.SkewZModOrder

open D5.S1.Dynamics.PeriodicOrbits.SkewAdditiveReturn
open Function

variable {X : Type*} {q : ℕ}

/-! A finite cyclic fiber converts the abstract additive holonomy order into an
explicit integer quotient. This is the arithmetic form of the skew return law. -/
theorem skew_minimalPeriod_zmod (f : X → X) (c : X → ZMod q) (x : X) (a : ZMod q)
    [NeZero q] :
    minimalPeriod (skewStep f c) (x, a) =
      minimalPeriod f x *
        (q / Nat.gcd q (birkhoffSum f c (minimalPeriod f x) x).val) := by
  rw [skew_minimalPeriod]
  have horder :
      addOrderOf (birkhoffSum f c (minimalPeriod f x) x) =
        q / Nat.gcd q (birkhoffSum f c (minimalPeriod f x) x).val := by
    rw [← ZMod.natCast_zmod_val (birkhoffSum f c (minimalPeriod f x) x)]
    simpa using
      (ZMod.addOrderOf_coe
        (birkhoffSum f c (minimalPeriod f x) x).val (NeZero.ne q))
  rw [horder]

#print axioms skew_minimalPeriod_zmod

end D5.S1.Dynamics.PeriodicOrbits.SkewZModOrder

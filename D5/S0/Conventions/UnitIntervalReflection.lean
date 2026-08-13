/- GID: D5/S0/Conventions/UnitIntervalReflection
   generality: G
   mirror-B: D5/B/S0/Conventions/UnitIntervalReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reflection about one half is an involution on the closed unit interval. -/

import Mathlib.Topology.UnitInterval

namespace D5.S0.Conventions.UnitIntervalReflection

/-- Applying the exchange `s -> 1 - s` twice returns every point of the unit interval. -/
theorem unit_interval_reflection_involutive (s : unitInterval) :
    unitInterval.symm (unitInterval.symm s) = s :=
  unitInterval.symm_involutive s

/-- The quantified unit-interval domain is inhabited. -/
example : unitInterval := 0

#print axioms unit_interval_reflection_involutive

end D5.S0.Conventions.UnitIntervalReflection

/- GID: D5/S0/Carrier/PrincipalIdeal
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: The golden integers form a principal ideal domain with unique factorization. -/

import D5.S0.Carrier.Euclidean
import Mathlib.RingTheory.PrincipalIdealDomain

namespace D5.S0.Carrier

/-- The golden integers form a principal ideal domain. -/
theorem golden_int_is_pid : IsPrincipalIdealRing GoldenInt := by
  infer_instance

/-- The golden integers form a unique factorization domain. -/
theorem golden_int_is_ufd : UniqueFactorizationMonoid GoldenInt := by
  infer_instance

end D5.S0.Carrier

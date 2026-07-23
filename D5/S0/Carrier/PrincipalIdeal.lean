/- GID: D5/S0/Carrier/PrincipalIdeal
   generality: I
   mirror-B: D5/B/S0/Carrier/Norm
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

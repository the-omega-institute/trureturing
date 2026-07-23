/- GID: D5/S0/Carrier/NormPowers
   generality: I
   mirror-B: D5/B/S0/Carrier/Norm
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: The golden norm sends every natural power to the corresponding integer power. -/

import D5.S0.Carrier.Norm

namespace D5.S0.Carrier

/-- The golden norm sends powers in `GoldenInt` to powers in `Int`. -/
theorem norm_pow (x : GoldenInt) (n : ℕ) : norm (x ^ n) = norm x ^ n := by
  exact normMonoidHom.map_pow x n

end D5.S0.Carrier

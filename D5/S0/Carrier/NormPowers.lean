/- GID: D5/S0/Carrier/NormPowers
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: The golden norm is power-multiplicative: the norm of a power is the power of the norm. -/

import D5.S0.Carrier.Norm

namespace D5.S0.Carrier

/-- The golden norm is power-multiplicative: `N(x ^ n) = N(x) ^ n`. This is the
    direct monoid-homomorphism consequence of `norm_mul`/`norm_one`, packaged as
    `normMonoidHom`, rather than a coordinate induction. -/
theorem norm_pow (x : GoldenInt) (n : ℕ) : norm (x ^ n) = norm x ^ n :=
  map_pow normMonoidHom x n

end D5.S0.Carrier

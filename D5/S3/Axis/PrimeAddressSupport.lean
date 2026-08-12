/- GID: D5/S3/Axis/PrimeAddressSupport
   generality: G
   mirror-B: D5/B/S3/Axis/PrimeAddressSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every nonzero finitely supported prime-address motion has a nonempty address. -/

import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace D5.S3.Axis.PrimeAddressSupport

/-- A prime address is a natural number together with its primality certificate. -/
abbrev PrimeAddress := {p : Nat // Nat.Prime p}

/-- A nonzero finitely supported motion on prime addresses has a nonempty address. -/
theorem nonempty_support_of_ne_zero {M : Type*} [Zero M]
    {motion : PrimeAddress →₀ M} (hmotion : motion ≠ 0) :
    motion.support.Nonempty :=
  Finsupp.support_nonempty_iff.mpr hmotion

end D5.S3.Axis.PrimeAddressSupport

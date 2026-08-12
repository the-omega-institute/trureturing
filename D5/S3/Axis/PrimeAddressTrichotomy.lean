/- GID: D5/S3/Axis/PrimeAddressTrichotomy
   generality: G
   mirror-B: D5/B/S3/Axis/PrimeAddressTrichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every prime is either two or has residue one or three modulo four. -/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

namespace D5.S3.Axis.PrimeAddressTrichotomy

/-- Every prime is either two or lies in one of the two odd residue classes modulo four. -/
theorem prime_address_mod_four_trichotomy (p : Nat) (hp : p.Prime) :
    p = 2 ∨ p % 4 = 1 ∨ p % 4 = 3 := by
  rcases hp.eq_two_or_odd with htwo | hodd
  · exact Or.inl htwo
  · exact Or.inr (Nat.odd_mod_four_iff.mp hodd)

end D5.S3.Axis.PrimeAddressTrichotomy

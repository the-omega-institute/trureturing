/- GID: D5/S0/Carrier/Powers/IntegerPowerNorm
   generality: I
   mirror-B: D5/B/S0/Carrier/Powers/IntegerPowerNorm
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Integral powers of the golden unit have the corresponding signed norm. -/

import D5.S0.Carrier.Units

namespace D5.S0.Carrier.Powers

open D5.S0.Carrier

/-- The norm parity law for `phiUnit` extends `norm_phi_pow` to all integer powers. -/
theorem norm_phiUnit_zpow (n : ℤ) :
    norm ((phiUnit ^ n : GoldenIntˣ).val) = (((-1 : ℤˣ) ^ n : ℤˣ) : ℤ) := by
  have hmap := (Units.map normMonoidHom).map_zpow phiUnit n
  have hval := congrArg Units.val hmap
  exact hval

example :
    norm ((phiUnit ^ (0 : ℤ) : GoldenIntˣ).val) = (((-1 : ℤˣ) ^ (0 : ℤ) : ℤˣ) : ℤ) := by
  exact norm_phiUnit_zpow 0

#print axioms norm_phiUnit_zpow

end D5.S0.Carrier.Powers

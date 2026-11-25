/- GID: D5/S0/Carrier/Powers/IntegerPowerNorm
   generality: I
   mirror-B: D5/B/S0/Carrier/Powers/IntegerPowerNorm
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Integral powers of the golden unit have the corresponding signed norm. -/

module
prelude
public import OmegaMath.Algebra.QuadraticExt.Units

namespace D5.S0.Carrier.Powers

open Omega Omega.QuadPoly

/-- The norm of a golden integer power is the corresponding power of minus one. -/
public theorem norm_phiUnit_zpow (n : Int) :
    Eq (norm intRing (signedGoldenPower .false n)) (intRing.powNat Int.one.neg n.natAbs) :=
  let generator : IntQuadPoly Int.one Int.one := alpha intRing
  let inverse := neg intRing (conj intRing generator)
  Int.rec (motive := fun k =>
    Eq (norm intRing (signedGoldenPower .false k)) (intRing.powNat Int.one.neg k.natAbs))
    (fun k => QuadPoly.norm_pow intRingLaws generator k)
    (fun k => QuadPoly.norm_pow intRingLaws inverse k.succ)
    n

example : Eq (norm intRing (signedGoldenPower .false Int.zero)) Int.one :=
  norm_phiUnit_zpow Int.zero

end D5.S0.Carrier.Powers

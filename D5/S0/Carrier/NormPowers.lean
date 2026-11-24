/- GID: D5/S0/Carrier/NormPowers
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: The golden norm is power-multiplicative: the norm of a power is the power of the norm. -/

module
prelude
public import OmegaMath.Algebra.QuadraticExt.Operations

namespace D5.S0.Carrier

open Omega Omega.QuadPoly

/-- The golden norm sends every natural power to the same power of the norm. -/
public theorem norm_pow (x : IntQuadPoly Int.one Int.one) (n : Nat) :
    Eq (norm intRing (pow intRing x n)) (intRing.powNat (norm intRing x) n) :=
  QuadPoly.norm_pow intRingLaws x n

end D5.S0.Carrier

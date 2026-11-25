/- GID: D5/S3/Arith/Primes/DivisorCharacterization
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The transparent natural prime divisor predicate and its standard interpretation. -/

module
prelude
public import OmegaMath.Arithmetic.Euclidean.Division
public import OmegaMathlib.Data.Nat.Prime.Defs

namespace D5.S3.Arith.Primes.DivisorCharacterization

open Omega Omega.Arithmetic

/-- A natural above one whose divisors are one and itself. -/
@[expose] public def IsPrime (p : Nat) : Prop :=
  And (Nat.lt Nat.one p) (∀ d, Dvd d p → Or (Eq d Nat.one) (Eq d p))

/-- Natural primality is equivalent to the transparent divisor characterization at every input. -/
public theorem isPrime_iff_prime (p : Nat) : Iff (IsPrime p) (OmegaMathlib.Nat.Prime p) :=
  Iff.intro (fun h => OmegaMathlib.Nat.prime_def.mpr h)
    (fun h => OmegaMathlib.Nat.prime_def.mp h)

end D5.S3.Arith.Primes.DivisorCharacterization

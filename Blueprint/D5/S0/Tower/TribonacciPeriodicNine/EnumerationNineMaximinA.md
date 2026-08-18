# Enumeration Nine Maximin A

## Abstract

Period-nine orbits A through M have a low arm at or below the champion value.

Two proof shapes are needed, not one. The recorded low state lies on the left branch of the arm minimum for fourteen orbits and on the right branch for twelve. Which branch applies was measured per orbit rather than assumed; an earlier draft used a different and wrong twelve, and the K case failed to close.

**Theorem 1.1 (Enumeration Nine Maximin A).**

$$\forall o \in \mathit{TribonacciCodedOrbit},\; o \in \mathit{tribonacciPeriodNineOrbitRepresentatives} \Rightarrow \operatorname{tribonacciPeriodicStateArm}\left(\operatorname{decodeTribonacciState}\left(\operatorname{lowState}\left(o\right)\right)\right) \le \operatorname{championValue}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineMaximinA.tribonacci_period_nine_orbit_a_low_arm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This converts into a theorem what the enumerator had only checked numerically, and it is what makes the certificates usable: no representative is a strict survivor.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineMaximinA.tribonacci_period_nine_orbit_a_low_arm`
- Dependency: [D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineValid](EnumerationNineValid.md)

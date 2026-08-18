# Enumeration Eleven MaximinD

## Abstract

Period-eleven Tribonacci certificates, part MaximinD.

The enumerator was calibrated against all three committed levels before use, and against their rotation classes as sets rather than their counts: it reproduces the fifteen, twenty-six and forty-two classes exactly.

**Theorem 1.1 (Enumeration Eleven MaximinD).**

$$\forall o \in \mathit{TribonacciCodedOrbit},\; o \in \mathit{tribonacciPeriodElevenOrbitRepresentatives} \Rightarrow \operatorname{tribonacciPeriodicStateArm}\left(\operatorname{decodeTribonacciState}\left(\operatorname{lowState}\left(o\right)\right)\right) \le \operatorname{championValue}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenMaximinD.tribonacci_period_eleven_orbit_46_low_arm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The left and right branch split of the arm minimum was measured for this level: thirty-nine left and thirty-five right. It differs at every level, so the shorter levels' sets are not reusable.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenMaximinD.tribonacci_period_eleven_orbit_46_low_arm`
- Dependency: [D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenMaximinC](EnumerationElevenMaximinC.md)
- Dependency: [D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenMaximinC](../TribonacciPeriodicTen/EnumerationTenMaximinC.md)

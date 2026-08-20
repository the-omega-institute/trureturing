# Enumeration Ten Maximin A

## Abstract

Period-ten orbits 01 through 14 have a low arm below the champion.

The enumerator was calibrated against both committed levels before use, and against their rotation classes as sets rather than their counts: it reproduces the fifteen period-eight classes and the twenty-six period-nine classes exactly.

**Theorem 1.1 (Enumeration Ten Maximin A).**

$$\forall o \in \mathit{TribonacciCodedOrbit},\; o \in \mathit{tribonacciPeriodTenOrbitRepresentatives} \Rightarrow \operatorname{tribonacciPeriodicStateArm}\left(\operatorname{decodeTribonacciState}\left(\operatorname{lowState}\left(o\right)\right)\right) \le \operatorname{championValue}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenMaximinA.tribonacci_period_ten_orbit_01_low_arm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two proof shapes are needed and the split differs from period nine: twenty-two low states sit on the left branch and twenty on the right. The right-branch set was measured for this level.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenMaximinA.tribonacci_period_ten_orbit_01_low_arm`
- Dependency: [D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineMaximinB](../TribonacciPeriodicNine/EnumerationNineMaximinB.md)
- Dependency: [D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenValidB](EnumerationTenValidB.md)

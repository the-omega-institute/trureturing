# Enumeration Ten Valid A

## Abstract

Period-ten orbits 01 through 22 are valid coded orbits.

The enumerator was calibrated against both committed levels before use, and against their rotation classes as sets rather than their counts: it reproduces the fifteen period-eight classes and the twenty-six period-nine classes exactly.

**Theorem 1.1 (Enumeration Ten Valid A).**

$$\forall o \in \mathit{TribonacciCodedOrbit},\; o \in \mathit{tribonacciPeriodTenOrbitRepresentatives} \Rightarrow \operatorname{tribonacciCodedOrbitValid}\left(o\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenValidA.tribonacci_period_ten_orbits_01_02_valid_and_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The tactic closure is the one the shorter levels use, reused verbatim rather than re-derived.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenValidA.tribonacci_period_ten_orbits_01_02_valid_and_nodup`
- Dependency: [D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineMaximinB](../TribonacciPeriodicNine/EnumerationNineMaximinB.md)
- Dependency: [D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenData](EnumerationTenData.md)

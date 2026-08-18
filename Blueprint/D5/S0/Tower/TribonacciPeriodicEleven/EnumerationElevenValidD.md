# Enumeration Eleven ValidD

## Abstract

Period-eleven Tribonacci certificates, part ValidD.

The enumerator was calibrated against all three committed levels before use, and against their rotation classes as sets rather than their counts: it reproduces the fifteen, twenty-six and forty-two classes exactly.

**Theorem 1.1 (Enumeration Eleven ValidD).**

$$\forall o \in \mathit{TribonacciCodedOrbit},\; o \in \mathit{tribonacciPeriodElevenOrbitRepresentatives} \Rightarrow \operatorname{tribonacciCodedOrbitValid}\left(o\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenValidD.tribonacci_period_eleven_representatives_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The left and right branch split of the arm minimum was measured for this level: thirty-nine left and thirty-five right. It differs at every level, so the shorter levels' sets are not reusable.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenValidD.tribonacci_period_eleven_representatives_valid`
- Dependency: [D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenValidC](EnumerationElevenValidC.md)
- Dependency: [D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenMaximinC](../TribonacciPeriodicTen/EnumerationTenMaximinC.md)

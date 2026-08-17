# Tribonacci Period-Seven Fixed-Point Base

## Abstract

The period-seven generator has seventy-one closed equations.

**Theorem 1.1 (Seventy-one period-seven fixed-point equations).**

$$\operatorname{length}\left(\operatorname{tribonacciFixedPointCodes}\left(7\right)\right) = 71$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSevenFixedBase.tribonacci_fixed_point_code_count_exactly_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A structural multiplier lemma reduces every length-seven denominator to one exact cubic norm computation.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSevenFixedBase.tribonacci_fixed_point_code_count_exactly_seven`
- Dependency: [D5/S0/Tower/TribonacciPeriodic/EnumerationSevenDisjoint](EnumerationSevenDisjoint.md)

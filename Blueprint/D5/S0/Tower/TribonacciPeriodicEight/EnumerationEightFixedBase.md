# Tribonacci Period-Eight Fixed-Point Base

## Abstract

The period-eight generator has one hundred thirty-one closed equations.

**Theorem 1.1 (One hundred thirty-one period-eight fixed-point equations).**

$$\operatorname{length}\left(\operatorname{tribonacciFixedPointCodes}\left(8\right)\right) = 131$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightFixedBase.tribonacci_fixed_point_code_count_exactly_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three closed-gap counts are eighty-one, thirteen, and thirty-seven; a shared multiplier lemma certifies the denominator.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightFixedBase.tribonacci_fixed_point_code_count_exactly_eight`
- Dependency: [D5/S0/Tower/TribonacciPeriodic/EnumerationSeven](../TribonacciPeriodic/EnumerationSeven.md)
- Dependency: [D5/S0/Tower/TribonacciPeriodic/EnumerationSixFixed](../TribonacciPeriodic/EnumerationSixFixed.md)
- Dependency: [D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightDisjoint](EnumerationEightDisjoint.md)

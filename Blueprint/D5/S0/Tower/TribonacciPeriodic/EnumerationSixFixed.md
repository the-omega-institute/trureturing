# Tribonacci Period-Six Fixed Points

## Abstract

Thirty-nine period-six equations reduce to inherited phases and five new cycles.

**Theorem 1.1 (Thirty-nine period-six fixed-point equations).**

$$\operatorname{length}\left(\operatorname{tribonacciFixedPointCodes}\left(6\right)\right) = 39$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSixFixed.tribonacci_fixed_point_code_count_exactly_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three-letter transition graph has thirty-nine closed, phase-marked words of length six.

**Theorem 1.2 (Period-six equations decompose into certified orbits).**

$$\operatorname{toFinset}\left(\operatorname{tribonacciFixedPointCodes}\left(6\right)\right) = \mathit{tribonacciExpectedPointCodesSix}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSixFixed.tribonacci_fixed_point_codes_six_decompose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Independent large, small, and combined gap checks identify all fixed codes with the inherited phases and thirty new phases.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSixFixed.tribonacci_fixed_point_code_count_exactly_six`
- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSixFixed.tribonacci_fixed_point_codes_six_decompose`
- Dependency: [D5/S0/Tower/TribonacciPeriodic/EnumerationSixDisjoint](EnumerationSixDisjoint.md)

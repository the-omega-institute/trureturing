# Enumeration Nine Data

## Abstract

Twenty-six exact primitive period-nine Tribonacci orbit certificates.

The twenty-six words are the primitive rotation classes among the two hundred forty phase-marked solutions of the period-nine equations. The enumerator was validated against the frozen period-eight data before use: it reproduces one hundred thirty-one phase points and fifteen primitive classes, and those fifteen rotation classes coincide with the committed ones as sets.

**Theorem 1.1 (Enumeration Nine Data).**

$$\operatorname{length}\left(\mathit{tribonacciPeriodNineOrbitRepresentatives}\right) = 26$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineData.tribonacci_period_nine_representative_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The count is the object-level claim: exactly twenty-six primitive rotation classes at period nine. Validity of each certificate is a separate statement in the companion module.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineData.tribonacci_period_nine_representative_count`
- Dependency: [D5/S0/Tower/TribonacciPeriodicEight/EnumerationEight](../TribonacciPeriodicEight/EnumerationEight.md)

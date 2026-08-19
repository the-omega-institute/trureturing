# Enumeration Nine Distinct

## Abstract

Period-nine phase codes have no duplicates inside a group of five and no overlap between groups.

Twenty-one statements: six saying the codes inside a group of five are distinct, and fifteen saying two different groups share no code. Grouping is forced by normalisation cost, which is also why the period-eight file groups by five.

**Theorem 1.1 (The first two groups share no code).**

$$\operatorname{Disjoint}\left(\operatorname{flatMap}\left(\mathit{orbitStates}, \mathit{tribonacciPeriodNineOrbitsFirst}\right), \operatorname{flatMap}\left(\mathit{orbitStates}, \mathit{tribonacciPeriodNineOrbitsSecond}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineDistinct.tribonacci_period_nine_first_second_state_codes_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assembling the twenty-one components into a single statement over the whole representative list is not done here. The components carry the content; the assembly is bookkeeping and remains open.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineDistinct.tribonacci_period_nine_first_second_state_codes_disjoint`
- Dependency: [D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineData](EnumerationNineData.md)
- Dependency: [D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineMaximinB](EnumerationNineMaximinB.md)

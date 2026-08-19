# Enumeration Ten Distinct B

## Abstract

Period-ten phase codes have no duplicates inside a group and no overlap between two groups.

Forty-five statements across two modules: nine saying the codes inside a group of five are distinct, and thirty-six saying two different groups share no code. Grouping by five is forced by normalisation cost, not chosen for style.

**Theorem 1.1 (Two period-ten groups share no code).**

$$\operatorname{Disjoint}\left(\operatorname{flatMap}\left(\mathit{orbitStates}, \mathit{tribonacciPeriodTenOrbitsThird}\right), \operatorname{flatMap}\left(\mathit{orbitStates}, \mathit{tribonacciPeriodTenOrbitsSeventh}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenDistinctB.tribonacci_period_ten_third_seventh_state_codes_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assembling the components into a single statement over the whole list is not done here, for the same reason it was left at period nine, and remains open.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenDistinctB.tribonacci_period_ten_third_seventh_state_codes_disjoint`
- Dependency: [D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenData](EnumerationTenData.md)
- Dependency: [D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenDistinctA](EnumerationTenDistinctA.md)

# Tribonacci Period-Eight Separation

## Abstract

The eleven inherited and one hundred twenty new period-eight codes are separated.

**Theorem 1.1 (Inherited and new period-eight phase codes are disjoint).**

$$\operatorname{Disjoint}\left(\mathit{tribonacciPeriodEightInheritedPhaseStates}, \mathit{tribonacciPeriodEightNewPhaseStates}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightDisjoint.tribonacci_inherited_new_state_codes_disjoint_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Three isolated five-orbit comparisons keep the separation check within the default tactic budget.

**Theorem 1.2 (All expected period-eight phase codes are distinct).**

$$\operatorname{Nodup}\left(\mathit{tribonacciPeriodEightExpectedPhaseStateList}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightDisjoint.tribonacci_period_eight_expected_state_codes_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The eleven divisor-period phases and one hundred twenty primitive phases combine into a duplicate-free list of one hundred thirty-one.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightDisjoint.tribonacci_inherited_new_state_codes_disjoint_eight`
- Truth anchor: `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightDisjoint.tribonacci_period_eight_expected_state_codes_nodup`
- Dependency: [D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightDistinct](EnumerationEightDistinct.md)

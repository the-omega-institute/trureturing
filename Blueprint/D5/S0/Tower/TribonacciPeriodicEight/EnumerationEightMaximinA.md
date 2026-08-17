# Tribonacci Period-Eight Maximin Bounds

## Abstract

All fifteen primitive period-eight orbits have low arms below the champion.

**Theorem 1.1 (Period-eight orbit A has a bounded low arm).**

$$\mathit{tribonacciPeriodEightOrbitALowArm} \le \operatorname{championValue}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightMaximinA.tribonacci_period_eight_orbit_a_low_arm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fifteen separate exact cubic comparisons keep every maximin witness within the default tactic budget.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightMaximinA.tribonacci_period_eight_orbit_a_low_arm`
- Dependency: [D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightFixed](EnumerationEightFixed.md)

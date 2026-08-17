# Tribonacci Period-Seven Maximin Bounds

## Abstract

All ten period-seven orbits have low arms below the champion.

**Theorem 1.1 (Period-seven orbit A has a bounded low arm).**

$$\mathit{tribonacciPeriodSevenOrbitALowArm} \le \operatorname{championValue}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSevenMaximinA.tribonacci_period_seven_orbit_a_low_arm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ten separate exact cubic comparisons keep each maximin witness within the default tactic budget.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSevenMaximinA.tribonacci_period_seven_orbit_a_low_arm`
- Dependency: [D5/S0/Tower/TribonacciPeriodic/EnumerationSevenFixed](EnumerationSevenFixed.md)

# Period Nine Aggregate

## Abstract

The period-at-most-nine enumeration has maximin exactly the champion value.

The period-nine level already carried validity, twenty-six per-orbit low-arm bounds, and pairwise distinctness. What it did not carry was the shape the optimality statement consumes: a cumulative representative list through period nine, and the membership of each recorded low state in its own orbit. Both are supplied here, and the aggregate follows by the same argument the period-eight level uses.

The consequence of the omission was that the source sentence's claim, that the enumeration up to period eleven exhibits the optimal cycle, had a formal counterpart only up to period eight. The parts existed at nine, ten and eleven; the conjunction over the cumulative list did not.

**Theorem 1.1 (Period nine maximin is the champion value).**

$$\operatorname{IsGreatest}\left(\mathit{tribonacciPeriodicOrbitMinimaNine}, \operatorname{championValue}\left(t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineAggregate.tribonacci_periodic_orbit_maximin_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The greatest element is attained by the period-two repeating orbit, which is inherited from the shorter levels rather than new at nine. What nine contributes is that none of its twenty-six new classes beats it.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineAggregate.tribonacci_periodic_orbit_maximin_nine`
- Dependency: [D5/S0/Tower/TribonacciPeriodicEight/EnumerationEight](../TribonacciPeriodicEight/EnumerationEight.md)
- Dependency: [D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineMaximinB](EnumerationNineMaximinB.md)

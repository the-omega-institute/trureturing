# Period Eleven Aggregate

## Abstract

The period-at-most-eleven enumeration has maximin exactly the champion value.

This level already carried its representative list and its aggregate low-arm bound, under names that do not follow the period-eight convention. Both were found by looking before building, and neither is rebuilt here.

What was missing is the pair that was missing at every level past eight: each recorded low state's membership in its own orbit, and the cumulative list with its optimality statement. The seventy-four new classes are joined to the period-at-most-ten list, and the argument is the one the period-eight level already uses.

**Theorem 1.1 (Period eleven maximin is the champion value).**

$$\operatorname{IsGreatest}\left(\mathit{tribonacciPeriodicOrbitMinimaEleven}, \operatorname{championValue}\left(t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenAggregate.tribonacci_periodic_orbit_maximin_eleven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The greatest element is the period-two repeating orbit, inherited from the shorter levels. What this level contributes is that none of its new classes beats it.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenAggregate.tribonacci_periodic_orbit_maximin_eleven`
- Dependency: [D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenMaximinE](EnumerationElevenMaximinE.md)
- Dependency: [D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenAggregate](../TribonacciPeriodicTen/EnumerationTenAggregate.md)

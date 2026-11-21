# The Subcritical Two-Mode Value

## Abstract

A maximum reachable cycle mean gives the original free-endpoint value in this family.

The vertices are the reachable real scores, starting at c. Each Alice loop gives a labelled edge to the next clipped score. Its weight is the exact change in the minimum payoff over all compatible Bob walks with free endpoints.

**Theorem 1.1 (Bounded error at finite horizons).**

Lean statement: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61CycleValue.maximin_cycle_estimate_of_hit`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61CycleValue.maximin_cycle_estimate_of_hit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonnegative subcritical toll and any uniform hitting bound, a reachable simple cycle attains a mean that bounds the average weight of every positive-length closed walk. For all sufficiently large horizons, the difference between the maximin and the horizon times that mean is bounded above and below by constants. A potential gives the upper bound. For the lower bound, reach the cycle from c, repeat it, and pad to the prescribed horizon.

**Theorem 1.2 (The original value is attained as a simple cycle mean).**

Lean statement: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61CycleValue.maximin_tendsto_cycleMean_subcritical`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61CycleValue.maximin_tendsto_cycleMean_subcritical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real toll satisfying 0 ≤ 2c < 1 + √2 admits a uniform Pell hitting bound. Dividing the finite-horizon estimate by the horizon gives convergence to the mean of a reachable simple cycle, and every reachable closed walk satisfies the corresponding upper bound.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61CycleValue.maximin_cycle_estimate_of_hit`
- Truth anchor: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61CycleValue.maximin_tendsto_cycleMean_subcritical`
- Dependency: [D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61Subcritical](MeyerovitchYoungQ61Subcritical.md)
- Dependency: [D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier](../../../S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.md)

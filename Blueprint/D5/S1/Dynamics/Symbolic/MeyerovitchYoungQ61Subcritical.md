# Free-Endpoint Scores for a Two-Mode Switching Game

## Abstract

An exact free-endpoint payoff recursion and a finite reachable state set at subcritical tolls.

This family specializes the value in equations (5) and (6) of Meyerovitch and Young, Rationality and computability of the covering radius for sofic shifts. Alice has one vertex and two loops with increments 1 and minus the square root of 2. Bob has two vertices with signs minus and plus and an edge for each ordered pair. The payoff is the source sign times half the increment plus the toll c on edges that switch mode. https://arxiv.org/html/2603.21449v1#S4.Ex38

**Theorem 1.1 (Both Bob endpoints are free).**

Lean statement: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61Subcritical.freeMinimum_edge_spec`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61Subcritical.freeMinimum_edge_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real toll, positive horizon and Alice word, the free minimum is the least element of the payoffs of compatible Bob edge walks. A Boolean vertex response determines exactly one such walk, and each walk determines its response with both endpoints included.

**Theorem 1.2 (Exact finite-horizon payoff).**

Lean statement: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61Subcritical.freeMinimum_eq_overshoot`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61Subcritical.freeMinimum_eq_overshoot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative toll and every Alice word prefix, the translated difference of the two terminal scores starts at c and follows the clipped update on [0, 2c]. Each overshoot reduces their average by half its size. Taking the lesser terminal score subtracts half the final absolute deviation from c.

**Theorem 1.3 (Uniform hitting of the open forbidden arc).**

Lean statement: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61Subcritical.uniformForbiddenHit_pell`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61Subcritical.uniformForbiddenHit_pell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If twice the toll is below the circumference, a common finite bound works for every phase in the allowed interval. Both increments advance by one modulo the circumference. A positive Pell return with sufficiently small displacement can be repeated to hit the strict interior of the forbidden arc at a positive time within that bound.

**Theorem 1.4 (Finite set of actual reachable scores).**

Lean statement: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61Subcritical.reachable_finset_of_hit`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61Subcritical.reachable_finset_of_hit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonnegative subcritical toll and any uniform hitting bound, each reachable state is determined by its last reset seed and an age strictly below the uniform hitting bound. The possible seeds are 0, c, and 2c. The allowed real interval injects into the circle, so there are at most three times the hitting bound many distinct reachable real scores.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61Subcritical.freeMinimum_edge_spec`
- Truth anchor: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61Subcritical.freeMinimum_eq_overshoot`
- Truth anchor: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61Subcritical.reachable_finset_of_hit`
- Truth anchor: `D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61Subcritical.uniformForbiddenHit_pell`
- Dependency: [D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ62](MeyerovitchYoungQ62.md)
- Dependency: [D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic](../../Words/Mechanical/SilverSlopeAbelianPellArithmetic.md)

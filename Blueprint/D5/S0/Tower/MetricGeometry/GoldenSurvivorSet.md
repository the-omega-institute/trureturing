# Golden Survivor Maximizer Set

## Abstract

Golden-survivor maximizers are exactly the midpoints of the largest internal gaps.

Restricting normalized distance to the golden-name hull turns the maximum value into a finite classification problem. The ordered grid has no hidden maximizers: equality forces both endpoint bounds to be sharp.

**Theorem 1.1 (One half is attained exactly at largest-gap midpoints).**

$$\forall Q \in N,\; \forall x \in R,\; \operatorname{memberOf}\left(x, \operatorname{goldenNameHull}\left(Q\right)\right) \Rightarrow \left(\operatorname{goldenSurvivor}\left(Q, x\right) = \frac{1}{2} \Leftrightarrow \left(\exists i \in \operatorname{internalGapIndex}\left(Q\right),\; \operatorname{isGoldenLargeGap}\left(Q, i\right) \land x = \operatorname{goldenGapMidpoint}\left(Q, i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/MetricGeometry/GoldenSurvivorSet.goldenSurvivor_eq_half_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a point in one adjacent cell, distance to each endpoint bounds infimum distance. Equality at one half makes both inequalities equalities, so the cell is large and the point is its midpoint. Conversely, strict grid order puts every grid point outside a large gap, making its midpoint exactly half a large gap from the grid.

**Theorem 1.2 (Maximizers and largest internal gaps have equal cardinality).**

$$\forall Q \in N,\; Q \ge 1 \Rightarrow \operatorname{ncard}\left(\operatorname{goldenSurvivorMaximizers}\left(Q\right)\right) = \operatorname{card}\left(\operatorname{goldenLargeGapIndices}\left(Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/MetricGeometry/GoldenSurvivorSet.golden_survivor_maximizer_ncard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Gap midpoints are strictly increasing, hence injective. The iff theorem identifies the maximizer set with the image of the filtered internal gap indices, so finite image cardinality is preserved exactly.

**Theorem 1.3 (The full frequency counts internal gaps plus the terminal correction).**

$$\forall Q \in N,\; Q \ge 2 \Rightarrow \operatorname{card}\left(\operatorname{goldenLargeGapIndices}\left(Q\right)\right) + \operatorname{terminalLargeIndicator}\left(Q\right) = \operatorname{Fib}\left(Q + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/MetricGeometry/GoldenSurvivorSet.golden_internal_large_gap_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The internal gap embedding identifies its filtered image with the full large-gap filter after deleting the terminal boundary gap. The frozen full-gap frequency then supplies Fib(Q+1), with a one-or-zero terminal correction read from the frozen gap word.

**Theorem 1.4 (The level-four survivor has four maximizers).**

$$\operatorname{ncard}\left(\operatorname{goldenSurvivorMaximizers}\left(4\right)\right) = 4$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/MetricGeometry/GoldenSurvivorSet.golden_survivor_four_point_ncard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At level four the Fibonacci gap word ends in a large letter. Removing that terminal gap from the five full large gaps leaves four internal large gaps, and therefore exactly four maximizing hull points.

**Theorem 1.5 (The champion level has twelve metric maximizers).**

$$\operatorname{ncard}\left(\operatorname{goldenSurvivorMaximizers}\left(6\right)\right) = 12$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/MetricGeometry/GoldenSurvivorSet.golden_survivor_champion_level_ncard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed-form champion point belongs to level six. At that level the full frequency has thirteen large gaps and the gap word again ends in a large letter, leaving twelve internal maximizing midpoints. Thus this metric maximizer set is not the source's separate four-state dynamical survivor orbit.

## References

- Truth anchor: `D5/S0/Tower/MetricGeometry/GoldenSurvivorSet.goldenSurvivor_eq_half_iff`
- Truth anchor: `D5/S0/Tower/MetricGeometry/GoldenSurvivorSet.golden_internal_large_gap_count`
- Truth anchor: `D5/S0/Tower/MetricGeometry/GoldenSurvivorSet.golden_survivor_champion_level_ncard`
- Truth anchor: `D5/S0/Tower/MetricGeometry/GoldenSurvivorSet.golden_survivor_four_point_ncard`
- Truth anchor: `D5/S0/Tower/MetricGeometry/GoldenSurvivorSet.golden_survivor_maximizer_ncard`
- Dependency: [D5/S0/Tower/GoldenGapWord](../GoldenGapWord.md)
- Dependency: [D5/S0/Tower/MetricGeometry/GoldenSurvivor](GoldenSurvivor.md)

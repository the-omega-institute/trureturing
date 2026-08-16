# Golden Survivor Extremality

## Abstract

Golden-name grid distance has an exact global normalized supremum on its hull.

The level-Q golden-name grid is the finite image of indexedNameValue. Because this image is finite, distance to it is unbounded on the whole real line. The natural global domain is therefore its hull, tiled by the closed intervals between consecutive indexed values.

**Theorem 1.1 (The golden grid is the intrinsic name-value image).**

$$\forall Q \in N,\; \operatorname{goldenNameGrid}\left(Q\right) = \operatorname{range}\left(\operatorname{nameValue}\left(Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/MetricGeometry/GoldenSurvivor.goldenNameGrid_eq_nameValue_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen equivalence between the Fibonacci interval and GoldenName is surjective in both directions, so the indexed and intrinsic descriptions determine exactly the same real grid.

**Definition 1.2 (Normalized golden survivor carrier).**

$$\forall Q \in N,\; \forall x \in R,\; \operatorname{goldenSurvivor}\left(Q, x\right) = \mathit{phi}^{Q} \cdot \operatorname{infDist}\left(x, \operatorname{goldenNameGrid}\left(Q\right)\right)$$

*Formalization.* `D5/S0/Tower/MetricGeometry/GoldenSurvivor.goldenSurvivor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier multiplies metric infimum distance to the actual finite golden-name grid by phi to the level. This is the direct golden analogue of normalized radixDistance.

**Theorem 1.3 (Every hull point has survivor value at most one half).**

$$\forall Q \in N,\; \forall x \in R,\; \operatorname{memberOf}\left(x, \operatorname{goldenNameHull}\left(Q\right)\right) \Rightarrow \operatorname{goldenSurvivor}\left(Q, x\right) \le \frac{1}{2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/MetricGeometry/GoldenSurvivor.goldenSurvivor_le_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each hull point lies in an adjacent golden cell. Distance to one of the two endpoints is at most half that cell length, and the frozen two-gap theorem bounds every cell by phi to the minus Q. Normalization therefore gives the global one-half ceiling.

**Theorem 1.4 (The first large-gap midpoint realizes one half).**

$$\forall Q \in N,\; Q \ge 1 \Rightarrow \operatorname{goldenSurvivor}\left(Q, \operatorname{firstGoldenMidpoint}\left(Q\right)\right) = \frac{1}{2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/MetricGeometry/GoldenSurvivor.first_golden_midpoint_realizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first adjacent gap has exact length phi to the minus Q. Strict monotonicity places every other grid point outside that gap, so its midpoint is exactly half a large gap from the entire grid.

**Theorem 1.5 (The global golden survivor supremum is one half).**

$$\forall Q \in N,\; Q \ge 1 \Rightarrow \operatorname{sSup}\left(\operatorname{goldenSurvivorBounds}\left(Q\right)\right) = \frac{1}{2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/MetricGeometry/GoldenSurvivor.golden_survivor_global_sup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pointwise theorem bounds every attainable lower value by one half. The first large-gap midpoint belongs to the hull and attains one half, so the supremum of all realized lower values is exactly one half at every positive level.

**Theorem 1.6 (The closed-form golden champion realizes the level-six maximum).**

$$\operatorname{goldenSurvivor}\left(6, \frac{13}{2} - 4 \cdot \mathit{phi}\right) = \frac{1}{2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/MetricGeometry/GoldenSurvivor.golden_champion_point_realizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen champion identity identifies thirteen halves minus four phi with phi to the minus six divided by two. That is the first level-six large-gap midpoint, so it realizes the global maximum.

## References

- Truth anchor: `D5/S0/Tower/MetricGeometry/GoldenSurvivor.first_golden_midpoint_realizes`
- Truth anchor: `D5/S0/Tower/MetricGeometry/GoldenSurvivor.goldenNameGrid_eq_nameValue_range`
- Truth anchor: `D5/S0/Tower/MetricGeometry/GoldenSurvivor.goldenSurvivor`
- Truth anchor: `D5/S0/Tower/MetricGeometry/GoldenSurvivor.goldenSurvivor_le_half`
- Truth anchor: `D5/S0/Tower/MetricGeometry/GoldenSurvivor.golden_champion_point_realizes`
- Truth anchor: `D5/S0/Tower/MetricGeometry/GoldenSurvivor.golden_survivor_global_sup`
- Dependency: [D5/S0/Tower/GoldenChampionPoint](../GoldenChampionPoint.md)
- Dependency: [D5/S0/Tower/GoldenGaps](../GoldenGaps.md)

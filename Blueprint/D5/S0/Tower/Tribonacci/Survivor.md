# Tribonacci Survivor Extremality

## Abstract

Tribonacci-name grid distance has a sharp normalized bound on its hull.

The level-Q grid is the finite image of the frozen increasing name-value enumeration. Its natural hull is tiled by the closed cells between consecutive values.

**Theorem 1.1 (The Tribonacci grid is the intrinsic name-value image).**

$$\forall Q \in N,\; \operatorname{tribonacciNameGrid}\left(Q\right) = \operatorname{range}\left(\operatorname{tribonacciNameValue}\left(Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Survivor.tribonacciNameGrid_eq_nameValue_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen equivalence between the Tribonacci counting interval and admissible names is surjective in both directions, so the indexed and intrinsic descriptions have the same image.

**Definition 1.2 (Normalized Tribonacci survivor carrier).**

$$\forall Q \in N,\; \forall x \in R,\; \operatorname{tribonacciSurvivor}\left(Q, x\right) = t^{Q} \cdot \operatorname{infDist}\left(x, \operatorname{tribonacciNameGrid}\left(Q\right)\right)$$

*Formalization.* `D5/S0/Tower/Tribonacci/Survivor.tribonacciSurvivor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier reuses the frozen Tribonacci constant t and multiplies metric infimum distance to the actual finite grid by t to the level.

**Theorem 1.3 (Every Tribonacci hull point has survivor value at most one half).**

$$\forall Q \in N,\; \forall x \in R,\; Q \ge 3 \Rightarrow \left(\operatorname{memberOf}\left(x, \operatorname{tribonacciNameHull}\left(Q\right)\right) \Rightarrow \operatorname{tribonacciSurvivor}\left(Q, x\right) \le \frac{1}{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Survivor.tribonacciSurvivor_le_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every point lies in an adjacent cell and is within half that cell's length of an endpoint. The exact three-gap spectrum and its strict ordering identify t^-Q as the largest cell length, so t^Q normalization gives one half.

**Theorem 1.4 (The first Tribonacci-gap midpoint realizes one half).**

$$\forall Q \in N,\; Q \ge 3 \Rightarrow \operatorname{tribonacciSurvivor}\left(Q, \operatorname{firstTribonacciMidpoint}\left(Q\right)\right) = \frac{1}{2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Survivor.first_tribonacci_midpoint_realizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed first indexed gap has length t^-Q by the frozen prefix recursion. Strict monotonicity places every other grid point outside that gap, making its midpoint exactly half a maximal gap from the grid.

## References

- Truth anchor: `D5/S0/Tower/Tribonacci/Survivor.first_tribonacci_midpoint_realizes`
- Truth anchor: `D5/S0/Tower/Tribonacci/Survivor.tribonacciNameGrid_eq_nameValue_range`
- Truth anchor: `D5/S0/Tower/Tribonacci/Survivor.tribonacciSurvivor`
- Truth anchor: `D5/S0/Tower/Tribonacci/Survivor.tribonacciSurvivor_le_half`
- Dependency: [D5/S0/Tower/Tribonacci/Gaps](Gaps.md)

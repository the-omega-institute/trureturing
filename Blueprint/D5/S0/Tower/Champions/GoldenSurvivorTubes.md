# Golden Backward Survivor Tubes

## Abstract

Golden backward survival is an exact four-branch contracting system after two steps.

A state records a golden gap kind and its normalized coordinate. The transition follows one refinement step, and finite survival is defined recursively by intersecting the threshold domain with the preimage of the preceding survivor set.

**Theorem 1.1 (Backward survival uses transition preimages).**

$$\forall F \in \mathit{GoldenSurvivorStateSet}, n \in N,\; \operatorname{goldenBackwardSurvivor}\left(F, n + 1\right) = \operatorname{intersection}\left(F, \operatorname{preimage}\left(\mathit{goldenTransition}, \operatorname{goldenBackwardSurvivor}\left(F, n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenSurvivorTubes.golden_backward_survivor_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The successor is F intersected with the inverse image of the previous depth. This is the T inverse direction; a forward image would be a different recurrence and would not express continued survival.

**Theorem 1.2 (Four inverse branches contract by the golden inverse).**

$$\forall b \in \mathit{GoldenBackwardBranch}, u \in R, v \in R,\; \operatorname{goldenFiberDistance}\left(\operatorname{goldenBranchSourceKind}\left(b\right), \operatorname{goldenBranchCoordinate}\left(b, u\right), \operatorname{goldenBranchCoordinate}\left(b, v\right)\right) = \mathit{goldenInverse} \cdot \operatorname{goldenFiberDistance}\left(\operatorname{goldenBranchTargetKind}\left(b\right), u, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenSurvivorTubes.golden_backward_branch_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Large and small coordinates use physical gap-length weights. In this metric each active affine inverse branch has contraction ratio exactly phi inverse, and therefore in particular at most that value.

**Theorem 1.3 (Forty inverse steps have a certified radius bound).**

$$\mathit{goldenInverse}^{40} < \frac{5}{1000000000}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenSurvivorTubes.golden_depth_forty_contraction_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The calculation first proves phi inverse is below 619/1000 and then checks the fortieth rational power. The resulting bound is 5e-9, which makes the source's order-of-1e-9 estimate precise.

**Theorem 1.4 (Strict backward survival is exactly four open tubes).**

$$\forall n \in N, s \in \mathit{GoldenSurvivorState},\; s \in \operatorname{goldenBackwardSurvivor}\left(\mathit{goldenStrictSurvivorSet}, n + 2\right) \Leftrightarrow \operatorname{goldenOpenTube}\left(n, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenSurvivorTubes.golden_backward_survivor_four_tubes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After the two-level transient, exact interval algebra identifies every finite-depth strict survivor with one of four open tubes. Their lower endpoints follow the four inverse branches and their upper endpoints are the four claimed limiting coordinates.

Four compile-time examples independently evaluate the transition on the tail point and the three cycle points. They verify the chain L(phi inverse over 2) to L(1/2) to L(phi/2) to S(1/2) and back to L(1/2).

## References

- Truth anchor: `D5/S0/Tower/Champions/GoldenSurvivorTubes.golden_backward_branch_contraction`
- Truth anchor: `D5/S0/Tower/Champions/GoldenSurvivorTubes.golden_backward_survivor_four_tubes`
- Truth anchor: `D5/S0/Tower/Champions/GoldenSurvivorTubes.golden_backward_survivor_succ`
- Truth anchor: `D5/S0/Tower/Champions/GoldenSurvivorTubes.golden_depth_forty_contraction_lt`
- Dependency: [D5/S0/Tower/GoldenGapWord](../GoldenGapWord.md)
- Dependency: [D5/S0/Tower/MetricGeometry/GoldenSurvivor](../MetricGeometry/GoldenSurvivor.md)

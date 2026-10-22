# Biased Native Frontier Distance

## Abstract

Directional cylinder weights give a bounded native frontier distance satisfying the triangle inequality.

**Definition 1.1 (Directional Cylinder Weight).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.weight`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty address has weight one. Prefixing a left edge multiplies by theta; prefixing a right edge multiplies by one minus theta. Thus each address has weight theta to its left-edge count times one minus theta to its right-edge count.

**Definition 1.2 (Pair Frontier Mass).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.distance`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.distance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any real theta and two finite native sources, distance is the sum of directional weights over their existing first-disagreement frontier. Left is false and right is true. Equal sources contribute zero, distinct root replies contribute one, and common branches split into the two weighted child distances.

**Theorem 1.3 (Triangle Inequality).**

$$\forall theta: \mathbb{R}, (0 \leq theta) \Rightarrow (theta \leq 1) \Rightarrow \forall s: \operatorname{Source}\left(\right), \forall z: \operatorname{Source}\left(\right), \forall t: \operatorname{Source}\left(\right), \operatorname{distance}\left(theta, s, t\right) \leq \operatorname{distance}\left(theta, s, z\right) + \operatorname{distance}\left(theta, z, t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.biased_frontier_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real theta in the closed unit interval and all finite native sources s,z,t, the distance from s to t is at most the sum of the distances through z. Structural induction on the first source, with the other two arbitrary, handles the three common-branch case by the child inequalities and nonnegative weights. Mixed roots use the bound by one and nonnegativity.

**Theorem 1.4 (Probability Bounds).**

$$\forall theta: \mathbb{R}, (0 \leq theta) \Rightarrow (theta \leq 1) \Rightarrow \forall s: \operatorname{Source}\left(\right), \forall t: \operatorname{Source}\left(\right), 0 \leq \operatorname{distance}\left(theta, s, t\right) \land \operatorname{distance}\left(theta, s, t\right) \leq 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.biased_frontier_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real theta in the closed unit interval and every source pair, the frontier distance lies between zero and one. All directional cylinder weights are nonnegative. Structural induction uses theta plus one minus theta equals one at a common branch.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.biased_frontier_bounds`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.biased_frontier_triangle`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.distance`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.weight`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation](../ActualImageAlphaSeparation.md)

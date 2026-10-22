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

**Theorem 1.5 (Exact Positive-Shift Frontier).**

$$\forall a: \mathbb{N}, (1 \leq a) \Rightarrow \forall t: \operatorname{Source}\left(\right), \operatorname{frontier}\left(t, \operatorname{iterate}\left(\operatorname{rho}\left(\right), a, t\right)\right) = \operatorname{leafAddresses}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.frontier_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural a at least one and every source t, the frontier between t and rho iterated a times on t is exactly the set of original leaves of t. The right-spine rank increases by a, excluding equality at each original leaf. Iterated substitution preserves every original branch, so structural induction identifies the entire frontier.

**Theorem 1.6 (Weighted Leaf Partition).**

$$\forall theta: \mathbb{R}, \forall t: \operatorname{Source}\left(\right), \operatorname{sum}\left(\operatorname{leafAddresses}\left(t\right), \operatorname{weight}\left(theta\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.leaf_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real theta and arbitrary finite full binary source t, the sum of directional weights of its leaves equals one. This algebraic identity includes uneven trees and follows by structural induction and the two directional weight factors.

**Theorem 1.7 (Unit Distance to Every Positive Shift).**

$$\forall theta: \mathbb{R}, \forall a: \mathbb{N}, (1 \leq a) \Rightarrow \forall t: \operatorname{Source}\left(\right), \operatorname{distance}\left(theta, t, \operatorname{iterate}\left(\operatorname{rho}\left(\right), a, t\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.distance_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real theta, every natural a at least one, and every finite source t, the biased distance from t to its a-fold native substitution is one. The exact leaf frontier and its weighted partition give the identity.

**Definition 1.8 (Three-Source Frontier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.tripleFrontier`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.tripleFrontier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Three common branches recurse on their respective left and right children. Three equal labelled leaves contribute nothing. Every other root combination contributes the empty address. This is the first disagreement of the three original reply traces.

**Definition 1.9 (Three-Source Normalized Mass).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.tripleMass`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.tripleMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three-source mass is the sum of the same directional weights over the three-source first-disagreement frontier.

**Theorem 1.10 (Exact Three-Shift Leaf Frontier).**

$$\forall a: \mathbb{N}, (1 \leq a) \Rightarrow \forall t: \operatorname{Source}\left(\right), \operatorname{tripleFrontier}\left(t, \operatorname{iterate}\left(\operatorname{rho}\left(\right), a, t\right), \operatorname{iterate}\left(\operatorname{rho}\left(\right), a, \operatorname{iterate}\left(\operatorname{rho}\left(\right), a, t\right)\right)\right) = \operatorname{leafAddresses}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.triple_frontier_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive a, the three sources t, rho iterated a times on t, and rho iterated twice a times on t have exactly the original leaf set of t as their joint first-disagreement frontier. The first two coordinates already disagree at every original leaf, and all three retain the original branches.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.biased_frontier_bounds`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.biased_frontier_triangle`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.distance`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.distance_shift`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.frontier_shift`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.leaf_partition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.tripleFrontier`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.tripleMass`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.triple_frontier_shift`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.weight`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation](../ActualImageAlphaSeparation.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection](../Observer/NativePrefixIdentityReflection.md)

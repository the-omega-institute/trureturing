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

**Definition 1.11 (Whole Shift-Copy Sources).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.U`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a supplied natural a, write S for rho iterated a times. U(a,x,y) is the ordered branch (x,(y,S(y))). Both occurrences use the same whole finite native value y.

**Definition 1.12 (The Complete Retained Input).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.Retained`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.Retained` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The old cut consists of the root with its complete one-hole row. The final epoch is a. The four literals say branch at the root and R, at epochs zero and a. The positive relation equates epoch-a RL with epoch-zero RR, retaining both endpoint guards. The two negative relations compare epoch-zero RL with RR and the epoch-zero root with L, retaining both guards of each sign. There are no further observations or image or rank conditions. The paid-source and complete-state premise belongs to the supplied acquisition interpretation; these statements concern all original finite sources satisfying its retained native record.

**Theorem 1.13 (The Entire Reconstructed Fiber).**

$$\forall a: \mathbb{N}, (1 \leq a) \Rightarrow \forall u: \operatorname{Source}\left(\right), (\operatorname{Retained}\left(a, u\right)) \iff (\exists x: \operatorname{Source}\left(\right), \exists y: \operatorname{Source}\left(\right), u = \operatorname{U}\left(a, x, y\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.retained_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a at least one, a finite native source satisfies the entire retained input exactly when it equals U(a,x,y) for some independent finite x and y. The zero-epoch literals expose both branches. The existing exact payload-history correspondence identifies the last hole with S(y). Positive shifts change right-spine rank, and positive leaf counts establish the two original negative comparisons. Every literal and every endpoint guard is retained in the converse.

**Definition 1.14 (Target Coordinates).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.position`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.position` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three indices zero, one and two name the original addresses L, RL and RR, in that order.

**Definition 1.15 (The Entire Target Cut).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.Q`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cut contains exactly L, RL and RR. It is prefix free and every one of its addresses is reached by every shift-copy source.

**Definition 1.16 (The Entire Target Exterior).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.exterior`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.exterior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal exterior is the ordered branch (hole L,(hole RL,hole RR)). It retains the whole outer source skeleton.

**Definition 1.17 (The Three Equality Partitions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.labelClass`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.labelClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Label zero identifies L with RL; label one identifies L with RR; label two makes all three holes distinct. The remaining hole in the first two labels is a singleton class.

**Definition 1.18 (Complete Target Records).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.label`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.label` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each label combines the entire exterior with all ordered pairs of equal-class holes, including the reflexive and reversed pairs. Thus absence of a reached pair records the corresponding whole-value disequality.

**Definition 1.19 (Parameters for Each Label).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.rowCondition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.rowCondition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For label zero, x equals y. For label one, x equals S(y). For label two, x differs from both y and S(y). Every finite y differs from S(y) for positive a.

**Definition 1.20 (Entire Canonical Row Strata).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.Stratum`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.Stratum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A stratum contains exactly the retained originals whose actual canonical target row agrees with a source having the selected complete literal record. The existing canonical-row equivalence identifies this with equality of the entire exterior and partition; no source payload is inserted into the row label.

**Theorem 1.21 (Exact Complete-Label Conditions).**

$$\forall a: \mathbb{N}, (1 \leq a) \Rightarrow \forall i: \operatorname{Fin}\left(3\right), \forall x: \operatorname{Source}\left(\right), \forall y: \operatorname{Source}\left(\right), (\operatorname{literalRecord}\left(\operatorname{Q}\left(\right), \operatorname{U}\left(a, x, y\right)\right) = \operatorname{label}\left(i\right)) \iff (\operatorname{rowCondition}\left(a, i, x, y\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.label_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive a, each label of U(a,x,y) is equivalent to its displayed row condition. The exterior has all three holes, and the finite partition tests every pair of complete subtree values. Positive-shift separation prevents the last two holes from agreeing.

**Theorem 1.22 (Every Original in Each Entire Stratum).**

$$\forall a: \mathbb{N}, (1 \leq a) \Rightarrow \forall i: \operatorname{Fin}\left(3\right), \forall u: \operatorname{Source}\left(\right), (\operatorname{Stratum}\left(a, i, u\right)) \iff (\exists x: \operatorname{Source}\left(\right), \exists y: \operatorname{Source}\left(\right), (u = \operatorname{U}\left(a, x, y\right)) \land (\operatorname{rowCondition}\left(a, i, x, y\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.stratum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive a and each of the three labels, membership is equivalent to being U(a,x,y) with precisely that label's parameter condition. Both directions use the full retained fiber and the existing equivalence between canonical rows and complete literal records. Parameters of different alternative originals remain independent.

**Theorem 1.23 (Exact Independent-Pair Decomposition).**

$$\forall theta: \mathbb{R}, \forall a: \mathbb{N}, \forall s: \operatorname{Source}\left(\right), \forall t: \operatorname{Source}\left(\right), \operatorname{distance}\left(theta, \operatorname{U}\left(a, s, s\right), \operatorname{U}\left(a, \operatorname{iterate}\left(\operatorname{rho}\left(\right), a, t\right), t\right)\right) = (((theta) \cdot (\operatorname{distance}\left(theta, s, \operatorname{iterate}\left(\operatorname{rho}\left(\right), a, t\right)\right))) + (((theta) \cdot (1 - theta)) \cdot (\operatorname{distance}\left(theta, s, t\right)))) + (((1 - theta)^{2}) \cdot (\operatorname{distance}\left(theta, \operatorname{iterate}\left(\operatorname{rho}\left(\right), a, s\right), \operatorname{iterate}\left(\operatorname{rho}\left(\right), a, t\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.pair_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real theta, natural a and independent finite s,t, the distance between U(a,s,s) and U(a,S(t),t) equals theta times A plus theta times one minus theta times B plus the square of one minus theta times C, where A is distance(s,S(t)), B is distance(s,t), and C is distance(S(s),S(t)). The three terms use the original-address prefixes L, RL and RR.

**Definition 1.24 (The Entire Binary-Product Value Set).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.pairValues`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.pairValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set contains distance(theta,u,v) for every retained original u in stratum zero and every independently chosen retained original v in stratum one. No parameters are identified across alternative originals.

**Theorem 1.25 (Attained Exact Binary-Product Infimum).**

$$\forall a: \mathbb{N}, (1 \leq a) \Rightarrow \forall theta: \mathbb{R}, (0 < theta) \Rightarrow (theta < 1) \Rightarrow \operatorname{IsLeast}\left(\operatorname{pairValues}\left(theta, a\right), \operatorname{min}\left(theta, 1 - theta\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.binary_product_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every supplied a at least one and every real zero less than theta less than one, min(theta,one minus theta) is the least element of the entire binary-product value set. Thus it is both the exact infimum and an attained value. The triangle inequality and unit positive-shift distances give A+B at least one and A+C at least one. The exact decomposition and zero at most A at most one give the lower bound for all independent parameters. Taking s=t attains theta; taking s=S(t) attains one minus theta.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.Q`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.Retained`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.Stratum`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.U`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.biased_frontier_bounds`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.biased_frontier_triangle`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.binary_product_minimum`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.distance`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.distance_shift`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.exterior`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.frontier_shift`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.label`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.labelClass`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.label_iff`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.leaf_partition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.pairValues`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.pair_decomposition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.position`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.retained_iff`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.rowCondition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.stratum_iff`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.tripleFrontier`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.tripleMass`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.triple_frontier_shift`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.weight`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation](../ActualImageAlphaSeparation.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativePayloadHistoryInstallation](../Observer/NativePayloadHistoryInstallation.md)

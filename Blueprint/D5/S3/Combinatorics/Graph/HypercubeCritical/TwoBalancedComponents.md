# Two actual components in a degree-three candidate

## Abstract

A 258-vertex degree-three candidate in Q9 contains two distinct balanced cubic components, each of size at least 48.

The external anchor is Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, Section 7, Problem 2, https://arxiv.org/html/2610.09483v1#Thmproblem2 : determine whether f₂(Q₉)=3 or 4. The theorem supplies a necessary condition for a 258-vertex candidate with induced maximum degree at most three. It establishes neither a candidate nor complete exclusion, so the original problem remains unresolved. Attainment of 48 and literature novelty are not established.

**Definition 1.1 (Projecting an actual component to cube vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/TwoBalancedComponents.componentFinset`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/TwoBalancedComponents.componentFinset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For U : Finset (Q 9), let G = (hypercube 9).induce (U : Set (Q 9)). For an actual K : G.ConnectedComponent, componentFinset U K is K.supp.toFinset.image Subtype.val. The consumed membership lemma identifies membership with a lift to U belonging to K.supp. Thus this projection retains the actual component identity and connectedness. It is nonempty, contained in U, and closed under cube adjacency to vertices of U; distinct components have disjoint projections.

**Theorem 1.2 (Two distinct balanced cubic components, with 96 vertices in their union).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/TwoBalancedComponents.exists_two_balanced_components`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/TwoBalancedComponents.exists_two_balanced_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The only hypotheses are U.card = 258 and G.degree x ≤ 3 for every x : (U : Set (Q 9)). The conclusion gives actual K,L : G.ConnectedComponent with K ≠ L and finite sets C = componentFinset U K and D = componentFinset U L. Both sets are nonempty, contained in U and disjoint, and each contains every U-neighbor of each of its vertices. Their actual induced cube graphs are regular of degree three and satisfy BalancedCriticalSpectrum.IsBalanced. Moreover 48 ≤ C.card, 48 ≤ D.card and 96 ≤ (C ∪ D).card. Balance uses the original FALSE-prefix Huang signing from Archive.Sensitivity, unchanged on the projected vertices; no signing conversion is assumed.

SupportedEigenDimension gives dimension at least two for ambient +3 eigenvectors vanishing outside U. Choose nonzero z and a root x with z(x) ≠ 0. SupportedEigenSaturation gives z(a) = M_ab z(b) on every actual U-edge, so vanishing propagates along actual induced walks. Consequently z is nonzero throughout the component K of x. The dimension bound also gives nonzero w vanishing at x; w vanishes throughout K, so a root y with w(y) ≠ 0 belongs to a different actual component L.

Saturation gives actual U-degree three at every nonzero coordinate and a switching function on the nonzero support. Component neighbor closure equates the cube neighbor intersections with the component and with U, preserving degree after projection. Restricting the same switching function proves balance. Apply BalancedCubeLowerBound.forty_eight_le_card to C and D; disjointness adds the two bounds to obtain 96.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/TwoBalancedComponents.componentFinset`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/TwoBalancedComponents.exists_two_balanced_components`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound](BalancedCubeLowerBound.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension](SupportedEigenDimension.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation](SupportedEigenSaturation.md)

# A local constraint on the common boundary of two balanced cubic sets

## Abstract

An exterior vertex meeting two separated balanced cubic Q9 sets has at most six neighbors in their union.

Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2), asks whether f₂(Q₉)=3 or 4. A 258-point candidate of induced maximum degree at most three must contain separated balanced cubic components. The theorem below restricts their common boundary; it does not construct or exclude a full candidate, establish attainment of the 48-point bound, or establish literature priority.

**Theorem 1.1 (At most six neighbors across two separated balanced cubic sets).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary.neighbor_card_add_le_six`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary.neighbor_card_add_le_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C,D be disjoint actual subsets of Q9, with no actual cube edge between them. Assume each induced graph is regular of degree three and each satisfies the original BalancedCriticalSpectrum.IsBalanced. For a vertex v outside both sets having at least one actual neighbor in each, the two neighbor counts sum to at most six. Connectedness and component-classification certificates are not hypotheses.

Exterior signed flow vanishes separately for each set, so both neighbor counts are positive and even. Their direction sets are disjoint, so a sum above six could only be eight. A two-direction side in a 2+6 split would force an induced degree at most two. In a 4+4 split, the four-direction auxiliary triangle-free graph has minimum degree two, forcing a four-cycle. Cubic regularity then forces each first-layer vertex's neighbor in the unique unused coordinate direction. Square relations and the absence of cross edges then again force a vertex of degree at most two, a contradiction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary.neighbor_card_add_le_six`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum](BalancedCriticalSpectrum.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth](BalancedCubeGirth.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation](SupportedEigenSaturation.md)

# The positive-gap Kozlov Perron-root ratio

## Abstract

At every positive integer gap and for every ground-set size at least four, the full proper transfer and the lattice transfer have positive complex spectral radii. The proper radius divided by the lattice radius is less than one.

**Definition 1.1 (The gap test).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall f \in \operatorname{FVector}\left(n\right),\; \operatorname{positiveGapCondition}\left(d, i, f\right) \Leftrightarrow \operatorname{val}\left(i\right) + 1 < \operatorname{indeg}\left(f\right) + d$$

*Formalization.* `D5/S3/Combinatorics/Kozlov/PositiveGapPerronRatio.positiveGapCondition` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

An index i of Fin(n) represents predecessor top degree i.val + 1. The first deficiency of the incoming vector f is indeg(f). The positive gap test is the strict inequality in equation (42) of Part III.

**Definition 1.2 (The full proper transfer).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall a \in \operatorname{ProperStates}\left(n\right),\; \forall b \in \operatorname{ProperStates}\left(n\right),\; \operatorname{P}\left(n, d, a, b\right) = \operatorname{count}\left(\operatorname{S}\left(n\right), a, b, d\right)$$

*Formalization.* `D5/S3/Combinatorics/Kozlov/PositiveGapPerronRatio.properPositiveGapTransfer` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The state set ProperStates(n) is the ordered list −1, 0, 1, …, n. S(n) is the set of distinct f-vectors of downsets on n vertices containing the empty face and all singletons. In count(X,a,b,d), row a is the predecessor top and column b is the incoming top. This is the cardinality of vectors f in X with top(f) = b and a < indeg(f) + d. The proper count is the transfer of Part II, Definition 28 and Theorem 41, after retaining just the proper vectors.

**Definition 1.3 (The lattice transfer).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall a \in \operatorname{LatticeStates}\left(n\right),\; \forall b \in \operatorname{LatticeStates}\left(n\right),\; \operatorname{L}\left(n, d, a, b\right) = \operatorname{count}\left(\operatorname{Lattice}\left(n\right), a, b, d\right)$$

*Formalization.* `D5/S3/Combinatorics/Kozlov/PositiveGapPerronRatio.latticePositiveGapTransfer` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

LatticeStates(n) consists of the positive degrees 1, …, n, represented by Fin(n). Lattice(n) consists of the integer vectors in the real convex hull of S(n). The transfer counts incoming vectors as in equation (42) and Corollary 33 of Part III.

**Theorem 1.4 (Strict comparison of the complex spectral radii).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \left(4 \le n \land 1 \le d\right) \Rightarrow \left(0 < \operatorname{radius}\left(\operatorname{complex}\left(\operatorname{P}\left(n, d\right)\right)\right) \land \left(0 < \operatorname{radius}\left(\operatorname{complex}\left(\operatorname{L}\left(n, d\right)\right)\right) \land \left(\operatorname{radius}\left(\operatorname{complex}\left(\operatorname{P}\left(n, d\right)\right)\right) < \operatorname{radius}\left(\operatorname{complex}\left(\operatorname{L}\left(n, d\right)\right)\right) \land \left(0 < \operatorname{toReal}\left(\operatorname{radius}\left(\operatorname{complex}\left(\operatorname{L}\left(n, d\right)\right)\right)\right) \land \frac{\operatorname{toReal}\left(\operatorname{radius}\left(\operatorname{complex}\left(\operatorname{P}\left(n, d\right)\right)\right)\right)}{\operatorname{toReal}\left(\operatorname{radius}\left(\operatorname{complex}\left(\operatorname{L}\left(n, d\right)\right)\right)\right)} < 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/PositiveGapPerronRatio.positive_gap_perron_root_ratio` (`✓ std3`). ∎

*Resolves.* `Problems/snellman-positive-gap-kozlov-perron-ratio` (proved) by `D5/S3/Combinatorics/Kozlov/PositiveGapPerronRatio.positive_gap_perron_root_ratio`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"snellman-positive-gap-kozlov-perron-ratio","declaration_gid":"D5/S3/Combinatorics/Kozlov/PositiveGapPerronRatio.positive_gap_perron_root_ratio","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

P and L are the counted transfers defined above. The radii are taken after casting every natural entry to the complex numbers. The function toReal reads the finite radius as a real number. The lattice radius is positive as a real denominator.

Complete skeletons supply consecutive transitions and loops in both positive-degree supports. In the full proper matrix the two columns of degrees −1 and 0 vanish, so adjoining these states adds only zero roots to the characteristic polynomial.

The lattice vector (1,n,2,1,0,…) has top three and first deficiency two. A three-element face would force at least three two-element faces, so this vector increases the lattice count in row one and column three. Pairing the matrix difference with a positive right vector of the proper block and a positive left vector of the lattice matrix gives a strictly positive sum.

## References

- Truth anchor: `D5/S3/Combinatorics/Kozlov/PositiveGapPerronRatio.latticePositiveGapTransfer`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/PositiveGapPerronRatio.positiveGapCondition`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/PositiveGapPerronRatio.positive_gap_perron_root_ratio`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/PositiveGapPerronRatio.properPositiveGapTransfer`
- Dependency: [D5/S3/Combinatorics/Graph/Pressure/WeightedWalks](../Graph/Pressure/WeightedWalks.md)
- Dependency: [D5/S3/Combinatorics/Kozlov/LatticeCount](LatticeCount.md)

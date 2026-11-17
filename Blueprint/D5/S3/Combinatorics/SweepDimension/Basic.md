# Finite-poset sweep lower bound

## Abstract

A finite-poset sweep system has at least as many orders as a maximum three-chain-free set.

**Definition 1.1 (Three-chain-free finite subsets).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Basic.ThreeChainFree`

*Formalization.* `D5/S3/Combinatorics/SweepDimension/Basic.ThreeChainFree` (`✓ std3`).

*Citation.* Paolo Boldi; Sebastiano Vigna (2026). *The lattice of antichains of intervals: Dyck paths, level sets, and sweep dimension*. DOI: [10.48550/arXiv.2610.41385](https://doi.org/10.48550/arXiv.2610.41385). URL: <https://arxiv.org/abs/2610.41385v1>.

*Commentary.*

A finite subset is three-chain-free when it contains no three elements a, b, c with a < b < c. This encodes the no-three-element-chain condition in Boldi–Vigna, Section 4.3, Proposition 3.

**Definition 1.2 (Maximum three-chain-free cardinality).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Basic.theta`

*Formalization.* `D5/S3/Combinatorics/SweepDimension/Basic.theta` (`✓ std3`).

*Citation.* Paolo Boldi; Sebastiano Vigna (2026). *The lattice of antichains of intervals: Dyck paths, level sets, and sweep dimension*. DOI: [10.48550/arXiv.2610.41385](https://doi.org/10.48550/arXiv.2610.41385). URL: <https://arxiv.org/abs/2610.41385v1>.

*Commentary.*

Theta is the maximum cardinality of a three-chain-free subset of the finite poset, as defined in Boldi–Vigna, Section 4.3, Proposition 3. Here the definition also applies to empty and singleton carriers.

**Definition 1.3 (Order-convex intervals).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Basic.IsInterval`

*Formalization.* `D5/S3/Combinatorics/SweepDimension/Basic.IsInterval` (`✓ std3`).

*Citation.* Paolo Boldi; Sebastiano Vigna (2026). *The lattice of antichains of intervals: Dyck paths, level sets, and sweep dimension*. DOI: [10.48550/arXiv.2610.41385](https://doi.org/10.48550/arXiv.2610.41385). URL: <https://arxiv.org/abs/2610.41385v1>.

*Commentary.*

An interval contains every point between each pair of its points. Empty and full subsets are included. This is the order-convex interval notion of Boldi–Vigna, Section 2.

**Definition 1.4 (Order-convex hull).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Basic.convexHull`

*Formalization.* `D5/S3/Combinatorics/SweepDimension/Basic.convexHull` (`✓ std3`).

*Citation.* Paolo Boldi; Sebastiano Vigna (2026). *The lattice of antichains of intervals: Dyck paths, level sets, and sweep dimension*. DOI: [10.48550/arXiv.2610.41385](https://doi.org/10.48550/arXiv.2610.41385). URL: <https://arxiv.org/abs/2610.41385v1>.

*Commentary.*

The convex hull of a finite set consists of all points lying between two of its elements. This is the hull used in the proof of Boldi–Vigna, Section 4.3, Proposition 3(2).

**Definition 1.5 (A carried linear order).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Basic.LinearOrderRel`

*Formalization.* `D5/S3/Combinatorics/SweepDimension/Basic.LinearOrderRel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A carried order relation is a binary relation together with a proof that it is a linear order on the carrier.

**Definition 1.6 (Sweep systems).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Basic.IsSweepSystem`

*Formalization.* `D5/S3/Combinatorics/SweepDimension/Basic.IsSweepSystem` (`✓ std3`).

*Citation.* Paolo Boldi; Sebastiano Vigna (2026). *The lattice of antichains of intervals: Dyck paths, level sets, and sweep dimension*. DOI: [10.48550/arXiv.2610.41385](https://doi.org/10.48550/arXiv.2610.41385). URL: <https://arxiv.org/abs/2610.41385v1>.

*Commentary.*

A family of k carried linear orders is a sweep system when every order-convex interval and every outside point admit one family order in which the outside point precedes every point of the interval. This formalizes Boldi–Vigna, Definition 1; the orders need not extend the poset order and may repeat.

**Lemma 1.7 (A maximum three-chain-free subset exists).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Basic.theta_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SweepDimension/Basic.theta_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Some three-chain-free finite subset has cardinality exactly theta.

**Theorem 1.8 (The lower bound for sweep systems).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Basic.theta_le_of_sweep`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SweepDimension/Basic.theta_le_of_sweep` (`✓ std3`). ∎

*Citation.* Paolo Boldi; Sebastiano Vigna (2026). *The lattice of antichains of intervals: Dyck paths, level sets, and sweep dimension*. DOI: [10.48550/arXiv.2610.41385](https://doi.org/10.48550/arXiv.2610.41385). URL: <https://arxiv.org/abs/2610.41385v1>.

*Commentary.*

Boldi–Vigna, Section 4.3, Proposition 3(3), proves theta at most sweep dimension for posets with at least two points, using the convex-hull restriction argument and distinct sweeps. Here the bound is expressed without taking a minimum: for every finite poset and every k-order sweep system, theta is at most k. The repository proof also covers empty and singleton carriers; those boundary cases extend the published statement's scope.

For a maximum three-chain-free set S and each y in S, the convex hull of S minus y omits y. The sweep condition therefore assigns an order putting y before all other members of S. One order cannot serve two distinct y, so the assignments inject S into the k orders.

The matching upper construction uses finite chain covers of the product with the two-element chain.

## References

- Truth anchor: `D5/S3/Combinatorics/SweepDimension/Basic.IsInterval`
- Truth anchor: `D5/S3/Combinatorics/SweepDimension/Basic.IsSweepSystem`
- Truth anchor: `D5/S3/Combinatorics/SweepDimension/Basic.LinearOrderRel`
- Truth anchor: `D5/S3/Combinatorics/SweepDimension/Basic.ThreeChainFree`
- Truth anchor: `D5/S3/Combinatorics/SweepDimension/Basic.convexHull`
- Truth anchor: `D5/S3/Combinatorics/SweepDimension/Basic.theta`
- Truth anchor: `D5/S3/Combinatorics/SweepDimension/Basic.theta_le_of_sweep`
- Truth anchor: `D5/S3/Combinatorics/SweepDimension/Basic.theta_witness`

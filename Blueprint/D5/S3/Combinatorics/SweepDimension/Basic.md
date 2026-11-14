# Finite-poset sweep lower bound

## Abstract

A finite-poset sweep system has at least as many orders as a maximum three-chain-free set.

**Definition 1.1 (Three-chain-free finite subsets).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Basic.ThreeChainFree`

*Formalization.* `D5/S3/Combinatorics/SweepDimension/Basic.ThreeChainFree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite subset is three-chain-free when it contains no three elements a, b, c with a < b < c.

**Definition 1.2 (Maximum three-chain-free cardinality).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Basic.theta`

*Formalization.* `D5/S3/Combinatorics/SweepDimension/Basic.theta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Theta is the maximum cardinality of a three-chain-free subset of the finite poset.

**Definition 1.3 (Order-convex intervals).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Basic.IsInterval`

*Formalization.* `D5/S3/Combinatorics/SweepDimension/Basic.IsInterval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An interval contains every point between each pair of its points. Empty and full subsets are included.

**Definition 1.4 (Order-convex hull).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Basic.convexHull`

*Formalization.* `D5/S3/Combinatorics/SweepDimension/Basic.convexHull` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The convex hull of a finite set consists of all points lying between two of its elements.

**Definition 1.5 (A carried linear order).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Basic.LinearOrderRel`

*Formalization.* `D5/S3/Combinatorics/SweepDimension/Basic.LinearOrderRel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A carried order relation is a binary relation together with a proof that it is a linear order on the carrier.

**Definition 1.6 (Sweep systems).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Basic.IsSweepSystem`

*Formalization.* `D5/S3/Combinatorics/SweepDimension/Basic.IsSweepSystem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A family of k carried linear orders is a sweep system when every order-convex interval and every outside point admit one family order in which the outside point precedes every point of the interval.

**Lemma 1.7 (A maximum three-chain-free subset exists).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Basic.theta_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SweepDimension/Basic.theta_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Some three-chain-free finite subset has cardinality exactly theta.

**Theorem 1.8 (The lower bound for sweep systems).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Basic.theta_le_of_sweep`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SweepDimension/Basic.theta_le_of_sweep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite poset and every k-order sweep system, theta is at most k. For a maximum three-chain-free set S and each y in S, the convex hull of S minus y omits y. The sweep condition therefore assigns an order putting y before all other members of S. One order cannot serve two distinct y, so the assignments inject S into the k orders.

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

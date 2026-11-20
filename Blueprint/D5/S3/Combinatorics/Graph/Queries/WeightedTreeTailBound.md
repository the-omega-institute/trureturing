# Summing the weighted crossing events over the leaves

## Abstract

The endpoint of a shortest forest suffix fixes its crossing index.

**Definition 1.1 (The bound determined by target depth).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/WeightedTreeTailBound.totalLeafWeight`

*Formalization.* `D5/S3/Combinatorics/Graph/Queries/WeightedTreeTailBound.totalLeafWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a target of depth d the total leaf weight is three halves minus the (d + 1)st power of one half, represented as an extended nonnegative real.

**Theorem 1.2 (Charge each arrival leaf at one crossing index).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/WeightedTreeTailBound.mass_of_weighted_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/WeightedTreeTailBound.mass_of_weighted_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a target vertex in the complete binary tree and a total path length r. For each index j and arrival leaf y, give crossing and tail events on the outcome type of a probability mass function. Measure events by its induced outer measure. Every outcome of the collision event belongs to both at a witness with j plus one plus the tree distance from y to the target equal to r.

Suppose the mass of each crossing event is bounded by a common budget. Suppose the joint mass of crossing and tail is bounded by the crossing mass times one half raised to the tree distance. Then the collision mass is at most the common budget times the total leaf weight for the target.

For a leaf in a coverage witness, the distance equation determines j. The collision event is contained in a union indexed by the leaves. Subadditivity and the joint mass bounds give the weighted sum. The exact binary tree distance sum evaluates it.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/WeightedTreeTailBound.mass_of_weighted_tail`
- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/WeightedTreeTailBound.totalLeafWeight`
- Dependency: [D5/S3/Combinatorics/Graph/Queries/BinaryTreeLeafDistance](BinaryTreeLeafDistance.md)

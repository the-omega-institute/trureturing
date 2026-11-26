# Three pair blocks and one triple block

## Abstract

A 72-point local saturation refutation in Q9

**Definition 1.1 (Universal weighted singularity implies a parity-side direction partition).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9LocalSaturation72Refutation.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9LocalSaturation72Refutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local implication ranges over a 72-point induced cubic Q9 support. Its premises are connectedness, Huang balance, and a nonzero kernel of the weighted defect on every parity side for every strictly positive independent coordinate weighting. Its conclusion asks for one parity whose neighbor-direction triples partition the nine axes at every row.

**Theorem 1.2 (The three-pair-one-triple support refutes the local implication).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9LocalSaturation72Refutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9LocalSaturation72Refutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support uses three pair blocks {0,1}, {2,3}, {4,5} and one triple block {6,7,8}. It contains 24 centres with one occupied coordinate in every block, 36 middle vertices omitting one pair block, and 12 leaves omitting one pair block and the triple block. The induced graph is cubic and connected, and its occupancy quotient is the seven-node tree with three length-two arms.

An explicit sign function on the vertices switches each induced edge to positive. The proof checks the signs on the finite set of cube flips and checks a spanning tree rooted at a centre.

For positive weights let Rᵢ be the squared-weight sum on pair block i, H the squared-weight sum on the triple block, R the sum of the Rᵢ, and s = R + H. On the even rows the polynomial kernel takes value R times the occupied-coordinate monomial at a centre and H Rᵢ times the monomial at a leaf of arm i. On the odd rows it takes value Rᵢ times the occupied-coordinate monomial at a middle vertex of arm i. The row and transpose equations are Mq = p and Mᵀp = s q, so both weighted defects have nonzero kernels for every strictly positive weight vector.

At a centre all three neighbor direction triples contain its occupied triple-block coordinate. At a middle vertex the two centre-neighbor triples share an occupied pair coordinate. These explicit rows fail the uniqueness clause on the false and true parity sides.

For Hong, Wu and Xia’s Problem 2, the local premises above are insufficient to select a Laurent parity side. The existence of a subcubic 258-point support in the nine-cube remains open. <https://arxiv.org/html/2610.09483v1#Thmproblem2>

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9LocalSaturation72Refutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9LocalSaturation72Refutation.result`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentDirectionTypes](../Laurent/Q9LaurentDirectionTypes.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedSaturation](../Q9WeightedSaturation.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedStarLift](../Q9WeightedStarLift.md)

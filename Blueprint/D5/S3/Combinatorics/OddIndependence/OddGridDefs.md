# Dense independent sets and four-neighbour crosses

## Abstract

The square grid and a vanishing density correction express the full-cross question of Caro, Petrusevski, Skrekovski and Tuza.

**Definition 1.1 (The square grid).**

Lean statement: `D5/S3/Combinatorics/OddIndependence/OddGridDefs.grid`

*Formalization.* `D5/S3/Combinatorics/OddIndependence/OddGridDefs.grid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yair Caro; Mirko Petruševski; Riste Škrekovski; Zsolt Tuza (2025). *The odd independence number of graphs, II: Finite and infinite grids and chessboard graphs*. URL: <https://arxiv.org/abs/2510.01897v1>.

*Commentary.*

For a natural number n, the graph is the Cartesian product of two paths on n vertices. Its vertices are pairs (a,b) with coordinates from zero through n-1. Two vertices are adjacent when one coordinate is equal and the other differs by one. Boundary vertices can have fewer than four neighbours.

**Definition 1.2 (The vanishing density correction).**

Lean statement: `D5/S3/Combinatorics/OddIndependence/OddGridDefs.claim`

*Formalization.* `D5/S3/Combinatorics/OddIndependence/OddGridDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yair Caro; Mirko Petruševski; Riste Škrekovski; Zsolt Tuza (2025). *The odd independence number of graphs, II: Finite and infinite grids and chessboard graphs*. URL: <https://arxiv.org/abs/2510.01897v1>.

*Commentary.*

There exists a real sequence epsilon indexed by the natural numbers and tending to zero such that, for every n at least one and every independent vertex set S of the n by n square grid, cardinality at least (3/8 + epsilon(n))n squared implies that some vertex has at least four neighbours and every one of its neighbours belongs to S. Since square-grid vertices have at most four neighbours, the conclusion is a full four-neighbour cross, including the requirement that its centre is an interior vertex.

## References

- Truth anchor: `D5/S3/Combinatorics/OddIndependence/OddGridDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/OddIndependence/OddGridDefs.grid`

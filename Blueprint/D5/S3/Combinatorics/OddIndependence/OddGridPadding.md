# From padded coordinates to square-grid neighbourhoods

## Abstract

Translation by two places a finite square-grid set in a zero-padded array and preserves full four-neighbour crosses.

**Definition 1.1 (The translated occupancy array).**

Lean statement: `D5/S3/Combinatorics/OddIndependence/OddGridPadding.padded`

*Formalization.* `D5/S3/Combinatorics/OddIndependence/OddGridPadding.padded` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yair Caro; Mirko Petruševski; Riste Škrekovski; Zsolt Tuza (2025). *The odd independence number of graphs, II: Finite and infinite grids and chessboard graphs*. URL: <https://arxiv.org/abs/2510.01897v1>.

*Commentary.*

For a finite vertex set S in the n by n square grid, padded(S,x,y) is true precisely when (x,y) is the translate (a+2,b+2) of some vertex (a,b) in S. It is false elsewhere. Thus rows and columns with coordinates zero or one are unoccupied, as are all positions with either coordinate at least n+2.

**Theorem 1.2 (A padded cross has an interior centre).**

Lean statement: `D5/S3/Combinatorics/OddIndependence/OddGridPadding.cross_of_padded`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OddIndependence/OddGridPadding.cross_of_padded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yair Caro; Mirko Petruševski; Riste Škrekovski; Zsolt Tuza (2025). *The odd independence number of graphs, II: Finite and infinite grids and chessboard graphs*. URL: <https://arxiv.org/abs/2510.01897v1>.

*Commentary.*

For any finite grid vertex set S and natural coordinates x,y, suppose the four padded positions (x,y+1), (x+1,y), (x+1,y+2), and (x+2,y+1) are occupied. There exists a vertex of the original grid with at least four neighbours, all belonging to S. The four positions translate back to distinct grid vertices surrounding the centre (x-1,y-1). Their coordinate bounds put this centre inside the grid, each of the four vertices is adjacent to it, and every neighbour of the centre is one of these four. Independence of S is not required for this implication.

## References

- Truth anchor: `D5/S3/Combinatorics/OddIndependence/OddGridPadding.cross_of_padded`
- Truth anchor: `D5/S3/Combinatorics/OddIndependence/OddGridPadding.padded`
- Dependency: [D5/S3/Combinatorics/OddIndependence/OddGridDefs](OddGridDefs.md)

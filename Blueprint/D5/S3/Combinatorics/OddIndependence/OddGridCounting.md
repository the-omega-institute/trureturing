# Ninefold counting of padded square-grid positions

## Abstract

Two layers of zero padding make every occupied position contribute to exactly nine three by three windows.

**Theorem 1.1 (Every occupied position occurs nine times).**

Lean statement: `D5/S3/Combinatorics/OddIndependence/OddGridCounting.ninefold_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OddIndependence/OddGridCounting.ninefold_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yair Caro; Mirko Petruševski; Riste Škrekovski; Zsolt Tuza (2025). *The odd independence number of graphs, II: Finite and infinite grids and chessboard graphs*. URL: <https://arxiv.org/abs/2510.01897v1>.

*Commentary.*

Let b be a Boolean array on pairs of natural numbers with all occupied positions in the coordinate range from 2 through n+1 in each direction. Sum the occupancy of b(i+r,j+c) over i,j from zero through n+1 and offsets r,c from zero through two. This integer sum is nine times the occupancy sum of b(x,y) over x,y from zero through n+1. For each of the nine offset pairs, shifting the two coordinate sums leaves their values unchanged: positions omitted at the lower ends and positions introduced at the upper ends are unoccupied. Equivalently, every occupied position lies in exactly three eligible windows in each coordinate direction, hence in nine windows altogether.

## References

- Truth anchor: `D5/S3/Combinatorics/OddIndependence/OddGridCounting.ninefold_count`

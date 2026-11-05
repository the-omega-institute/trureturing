# King boards, empty seams and square tilings

## Abstract

Finite free and toroidal king configurations, their coefficients, and square tilings.

OEIS A394697 uses the maximum coefficient of the independence polynomial of the full square torus. A063443 counts square tilings by unit and two-by-two squares and records their correspondence with free king boards of side one less. The free entropy and maximum-versus-total mechanisms are credited to Calkin, James and Purvis, Counting Kings, and Liang, arXiv:2505.12776v2, Proposition 3.1. The toroidal seam comparison retains both periodic coordinates and every integer side length.

**Definition 1.1 (Absolute coordinate difference).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.gap`

*Formalization.* `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.gap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

gap(a,b) is (a-b)+(b-a) in natural arithmetic, hence the usual absolute difference.

**Definition 1.2 (Free king adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.freeAdjacent`

*Formalization.* `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.freeAdjacent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two distinct coordinate pairs are adjacent when both coordinate gaps are at most one.

**Definition 1.3 (Periodic king adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.torusAdjacent`

*Formalization.* `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.torusAdjacent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two distinct coordinate pairs are adjacent when min(gap,n-gap) is at most one in both coordinates. The board bounds put both coordinates in zero through n minus one.

**Theorem 1.4 (An empty row and column remove wraparound edges).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.empty_seam_adjacency`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.empty_seam_adjacency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and coordinate pairs u and v whose four coordinates are less than n-1, toroidal adjacency is equivalent to free adjacency. The statement includes odd n and has no parity premise.

**Definition 1.5 (The square vertex set).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.board`

*Formalization.* `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.board` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

board(n) is the Cartesian product of two copies of Finset.range n.

**Definition 1.6 (The finite configuration family).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.independentSets`

*Formalization.* `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.independentSets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter the powerset of the specified finite board by the requirement that no ordered pair of its vertices is adjacent. The distinctness condition in king adjacency permits the empty configuration and does not create loops.

**Definition 1.7 (Free square configurations).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.freeCount`

*Formalization.* `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.freeCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

freeCount(n) counts all independent subsets of the free n by n king board.

**Definition 1.8 (Free rectangular configurations).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.rectangleCount`

*Formalization.* `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.rectangleCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rectangleCount(r,c) counts all independent subsets of range r times range c with free king adjacency.

**Definition 1.9 (Toroidal total count).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.torusCount`

*Formalization.* `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.torusCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

torusCount(n) counts all independent subsets of the full n by n toroidal king graph.

**Definition 1.10 (Cardinality coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.coefficient`

*Formalization.* `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.coefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

coefficient(n,k) is the number of toroidal independent sets of cardinality k, including zero coefficients and k=0.

**Definition 1.11 (The A394697 maximum).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.peak`

*Formalization.* `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.peak` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

peak(n) is the natural supremum of coefficient(n,k) for all k from zero through n squared, inclusive.

**Theorem 1.12 (Injecting the smaller free board).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.free_le_torus`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.free_le_torus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, freeCount(n-1) is at most torusCount(n). The same vertex subset is embedded with the final row and column empty.

**Theorem 1.13 (Forgetting periodic edges).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.torus_le_free`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.torus_le_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, torusCount(n) is at most freeCount(n). Every toroidal independent set is a free independent set on the same vertices.

**Theorem 1.14 (Polynomial loss from taking the maximum).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.count_le_mul_peak`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.count_le_mul_peak` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, torusCount(n) is at most (n squared plus one) times peak(n). The configuration family is partitioned by all n squared plus one possible cardinalities.

**Theorem 1.15 (A coefficient is bounded by the total).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.peak_le_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.peak_le_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, peak(n) is at most torusCount(n).

**Definition 1.16 (A two-by-two tile).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.squareTile`

*Formalization.* `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.squareTile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

squareTile(u) consists of the four cells with each coordinate equal to the corresponding coordinate of u or its successor.

**Definition 1.17 (Square tilings with implicit unit completion).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.tilingPlacements`

*Formalization.* `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.tilingPlacements` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For side m, choose lower-left coordinates in board(m-1) for pairwise disjoint two-by-two tiles. Every uncovered cell has its uniquely determined unit tile. This is an encoding of complete tilings, with no additional independent choices for unit tiles.

**Definition 1.18 (The literal A063443 count).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.a063443`

*Formalization.* `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.a063443` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

a063443(m) is the cardinality of the square-tiling placement family. Its free-board side is m minus one, as stated by OEIS A063443.

**Definition 1.19 (Recovering the full tile collection).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.tilingBlocks`

*Formalization.* `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.tilingBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take all selected squareTile blocks and one singleton tile for every cell of board(m) outside their union.

**Theorem 1.20 (The exact source index shift).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.tiling_free_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.tiling_free_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m, a063443(m)=freeCount(m-1). Two two-by-two tiles overlap exactly when both lower-left coordinate gaps are at most one; their distinct anchors therefore have exactly free king adjacency.

**Theorem 1.21 (Existence of the free square entropy).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.free_log_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.free_log_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists a nonnegative real s such that log(freeCount(n))/n squared converges to s through all natural n. Restricting at a straight cut proves rectangular submultiplicativity. Transposition gives symmetry, the empty configuration gives positivity, and all vertex subsets give the binary area bound. The rectangular entropy theorem supplies the square limit without assuming it.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.a063443`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.board`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.coefficient`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.count_le_mul_peak`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.empty_seam_adjacency`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.freeAdjacent`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.freeCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.free_le_torus`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.free_log_limit`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.gap`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.independentSets`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.peak`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.peak_le_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.rectangleCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.squareTile`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.tilingBlocks`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.tilingPlacements`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.tiling_free_identity`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.torusAdjacent`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.torusCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.torus_le_free`
- Dependency: [D5/S3/Combinatorics/Graph/RectangularCountEntropy](RectangularCountEntropy.md)

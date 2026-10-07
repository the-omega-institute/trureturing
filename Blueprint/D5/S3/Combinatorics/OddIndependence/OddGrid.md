# An affirmative answer to the square-grid full-cross question

## Abstract

Independent square-grid sets above density three eighths with correction four divided by the side length contain a full four-neighbour cross.

**Theorem 1.1 (A vanishing correction forces a full cross).**

Lean statement: `D5/S3/Combinatorics/OddIndependence/OddGrid.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OddIndependence/OddGrid.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yair Caro; Mirko Petruševski; Riste Škrekovski; Zsolt Tuza (2025). *The odd independence number of graphs, II: Finite and infinite grids and chessboard graphs*. URL: <https://arxiv.org/abs/2510.01897v1>.

*Commentary.*

Problem 29 of Caro, Petrusevski, Skrekovski and Tuza has an affirmative answer. Take epsilon(n)=4/n for positive n and epsilon(0)=0. This real sequence tends to zero. For every n at least one, an independent set S of the n by n square grid with cardinality at least (3/8 + 4/n)n squared contains all four neighbours of an interior vertex. Indeed, if S contains no full cross, translate it by two and fill the remaining array positions with zeros. The local discharge inequality and ninefold window counting yield 8 times the cardinality of S at most 3(n+2) squared. But (3/8 + 4/n)n squared is strictly greater than 3(n+2) squared divided by eight for every n at least one, giving a contradiction. A full cross in the padded array translates back to four distinct neighbours of an interior grid vertex, and every neighbour of that vertex belongs to S.

## References

- Truth anchor: `D5/S3/Combinatorics/OddIndependence/OddGrid.result`
- Dependency: [D5/S3/Combinatorics/OddIndependence/OddGridCertificate](OddGridCertificate.md)
- Dependency: [D5/S3/Combinatorics/OddIndependence/OddGridCounting](OddGridCounting.md)
- Dependency: [D5/S3/Combinatorics/OddIndependence/OddGridPadding](OddGridPadding.md)

# Boundary-Minimal Permutations and Their Placement Counts

## Abstract

Boundary-minimal permutations that are not skew-merged have two explicit shapes up to value complementation, and the first family has at least three placements.

**Theorem 1.1 (Two boundary-minimal shapes).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookBoundary.boundary_minimal_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookBoundary.boundary_minimal_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Let n be positive and let w be a permutation of zero through n minus one that is not skew-merged. Suppose that every occurrence of 2143 or 3412 contains the first position, the last position, the position of value zero, and the position of value n minus one. There is a permutation s equal to w or its value complement, with positions p and q satisfying zero less than p less than q less than n minus one, s(p) equal to zero, s(q) equal to n minus one, and s(0) less than s(n - 1). For some nonnegative integers a and b, n equals a plus b plus four, and one of two shapes holds. In the first, p equals a plus one, q equals n minus two, s(0) equals one, s(n - 1) equals b plus two, s(i) plus i equals n minus one for zero less than i less than p, and s(i) equals i minus p plus one for p less than i less than q. In the second, p equals one, q equals b plus two, s(0) equals a plus one, s(n - 1) equals n minus two, s(i) equals i minus p plus s(0) for p less than i less than q, and s(i) plus i equals n minus one for q less than i less than n minus one.

**Theorem 1.2 (At least three placements in the first family).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookBoundary.family_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookBoundary.family_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Let a and b be nonnegative integers and let n equal a plus b plus four. Suppose that the permutation w of zero through n minus one has the following values: w(0) equals one; w(i) equals n minus i minus one for one at most i at most a; w(a + 1) equals zero; w(i) equals i minus a for a plus one less than i less than a plus b plus two; w(a + b + 2) equals n minus one; and w(n - 1) equals b plus two. The permutation grid of w has at least three complete rook placements.

## References

- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookBoundary.boundary_minimal_classification`
- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookBoundary.family_count`
- Dependency: [D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookRegions](SkewMergedRookRegions.md)
- Dependency: [D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords](SkewMergedRookWords.md)

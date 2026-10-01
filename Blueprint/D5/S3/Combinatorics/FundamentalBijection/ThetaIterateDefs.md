# Iterated Pattern Avoidance and Its Counts

## Abstract

The avoidance layers count permutations whose initial orbit segments avoid a fixed pattern.

**Definition 1.1 (Avoidance through an iteration depth).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateDefs.iterateAvoiders`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateDefs.iterateAvoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

The layer of size n and depth k consists of permutations of one through n whose fundamental images at every iteration index from zero through k avoid the pattern sigma.

**Definition 1.2 (A cubic quasipolynomial).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateDefs.quadCount`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateDefs.quadCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

Write n = 3m + r with r zero, one, or two. The count is m cubed + 3m squared + 2m - 1 for r zero, m cubed + 4m squared + 4m for r one, and m cubed + 5m squared + 7m + 2 for r two, with subtraction in the nonnegative integers.

**Definition 1.3 (The proposed counts for 132-avoidance).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateDefs.claim`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

The second-layer count is the cubic quasipolynomial for every size at least two. For every size n at least three, the counts at depths three, four, and five are 3n - 4, 2n - 1, and n + 2 respectively, and the count at every depth at least six is five.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateDefs.iterateAvoiders`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateDefs.quadCount`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs](ThetaFixedDefs.md)

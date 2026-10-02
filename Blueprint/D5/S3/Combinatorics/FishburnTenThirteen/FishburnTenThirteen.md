# Enumeration of Two Fishburn Avoidance Classes

## Abstract

Two Fishburn avoidance classes have the same binomial-Catalan enumeration.

**Theorem 1.1 (The common binomial-Catalan count).**

Lean statement: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteen.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteen.result` (`✓ std3`). ∎

*Resolves.* `Problems/egge-fishburn-conjecture-10-13` (proved) by `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteen.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"egge-fishburn-conjecture-10-13","declaration_gid":"D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteen.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For every positive integer n, the number of Fishburn permutations of length n avoiding 2413 and 2431 equals the number avoiding 2431 and 3241, and both numbers equal the sum over k from one through n of the binomial coefficient choosing k minus one from n minus one multiplied by the Catalan number of index n minus k.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteen.result`
- Dependency: [D5/S1/Words/Patterns/A398542Polynomial](../../../S1/Words/Patterns/A398542Polynomial.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnCatalanBinomialDefs](../Fishburn/FishburnCatalanBinomialDefs.md)
- Dependency: [D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenAConstruction](FishburnTenThirteenAConstruction.md)
- Dependency: [D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBIndecomposable](FishburnTenThirteenBIndecomposable.md)

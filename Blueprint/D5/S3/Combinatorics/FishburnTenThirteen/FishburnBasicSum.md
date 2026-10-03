# The Fishburn Condition under Direct Sum

## Abstract

The Fishburn condition is preserved and reflected by direct sums with separated values.

**Theorem 1.1 (Componentwise Fishburn condition).**

Lean statement: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicSum.isFishburn_directSum_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicSum.isFishburn_directSum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let m be a nonnegative integer, let every entry of a word u be at most m, and let every entry of a word v be positive. The concatenation of u with the word obtained by increasing every entry of v by m is Fishburn if and only if both u and v are Fishburn.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicSum.isFishburn_directSum_iff`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicInsertion](../Fishburn/FishburnBasicInsertion.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum](../Nonnesting/NonnestingBasicSum.md)

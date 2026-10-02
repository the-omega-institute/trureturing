# Counting Component Boundaries

## Abstract

Direct-sum boundaries correspond to the ends of indecomposable permutation components.

**Theorem 1.1 (The number of separating cuts).**

Lean statement: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicComponentCuts.component_boundary_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicComponentCuts.component_boundary_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let parts be a list of nonempty sum-indecomposable permutations, each on the integers from one through its length, and let p be their iterated direct sum. Among the positions from zero through the length of p, the number of cuts for which every entry before the cut is less than every entry after it is the number of parts plus one. Both endpoint cuts are included.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicComponentCuts.component_boundary_count`
- Dependency: [D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicComponents](FishburnBasicComponents.md)

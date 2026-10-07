# Enumeration of Nonnesting Permutations Avoiding 1322

## Abstract

Nonnesting permutations avoiding 1322 have the asserted binomial enumeration.

**Theorem 1.1 (The 1322 enumeration).**

$$claim1322$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.result` (`✓ std3`). ∎

*Resolves.* `Problems/elizalde-luo-nonnesting-1322` (proved) by `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"elizalde-luo-nonnesting-1322","declaration_gid":"D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For every positive n, n times the number of nonnesting permutations of the multiset with two copies of each letter from one through n avoiding 1322 equals the sum, over k from zero through n minus one, of the product of the binomial coefficients choosing k from 3n and choosing n minus one from 2n minus k minus two.

**Theorem 1.2 (The reusable Lagrange coefficient supplier).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.lagrange_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.lagrange_coefficient` (`✓ std3`). ∎

*Citation.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

Let r and Φ be rational formal power series, with constantCoeff r = 0 and r = X times PowerSeries.subst r Φ. For natural n and k with 1 ≤ k ≤ n, the rational cast of n times coeff n (r^k) equals the rational cast of k times coeff (n − k) (Φ^n). This is the power specialization of Gessel’s Theorem 2.1.1, equation (2.1.1). The existing proof remains owned here; the original result and the Catalan bridge consume this one public theorem. Zero constant coefficient supplies HasSubst r; the proof handles n = k separately and cancels the rational cast of n − k only in the positive-difference case. This generic coefficient theorem carries no P13 enumeration or resolution claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.lagrange_coefficient`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.result`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoCount](NonnestingOneThreeTwoTwoCount.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoKernel](NonnestingOneThreeTwoTwoKernel.md)

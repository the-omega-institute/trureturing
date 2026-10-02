# Unique Direct-Sum Factorization

## Abstract

Every permutation has a unique factorization into nonempty sum-indecomposable permutations.

**Definition 1.1 (The sum of a sequence of factors).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumFactors.sumFactors`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumFactors.sumFactors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

The sum of an empty sequence of factors is empty; otherwise concatenate the first factor with the sum of the remaining factors after increasing every remaining value by the length of the first factor.

**Theorem 1.2 (Existence of indecomposable factors).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumFactors.exists_sum_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumFactors.exists_sum_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

Every permutation can be expressed as the sum of a sequence of nonempty permutations, each of which has no proper nonempty direct-sum cut.

**Theorem 1.3 (Uniqueness of indecomposable factors).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumFactors.sum_factorization_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumFactors.sum_factorization_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

Two sequences of nonempty sum-indecomposable permutations with the same direct sum are equal.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumFactors.exists_sum_factorization`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumFactors.sumFactors`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumFactors.sum_factorization_unique`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumIndecomp](ThetaBasicSumIndecomp.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum](../Nonnesting/NonnestingBasicSum.md)

# Rank-one Hadamard products and nonnegative diagonal weights

## Abstract

Rank-one Hadamard products and nonnegative diagonal weights.

**Theorem 1.1 (Outer-product factorization).**

Lean statement: `D5/S3/Quantum/Schatten/RankOneHadamard.exists_rank_one_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/RankOneHadamard.exists_rank_one_factors` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

Every complex square G of rank at most one has the form G=xyᵀ for two complex vectors x and y. The zero matrix and dimension zero are included.

**Theorem 1.2 (Common diagonal weights for both factors).**

Lean statement: `D5/S3/Quantum/Schatten/RankOneHadamard.rank_one_hadamard_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/RankOneHadamard.rank_one_hadamard_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex square G of rank at most one and every unitarily invariant norm N, there are nonnegative real vectors a and b such that, simultaneously for every W, N(W∘G)=N(diag(a)Wdiag(b)) and N(W⁻¹∘Gᵀ)=N(diag(a)(W⁻¹)*diag(b)). Factor G=xyᵀ and take aᵢ=|xᵢ| and bᵢ=|yᵢ|. Diagonal unitary phases remove the arguments of x and y, with phase one at zero; transpose and adjoint invariance identify the second factor.

## References

- Truth anchor: `D5/S3/Quantum/Schatten/RankOneHadamard.exists_rank_one_factors`
- Truth anchor: `D5/S3/Quantum/Schatten/RankOneHadamard.rank_one_hadamard_reduction`
- Dependency: [D5/S3/Quantum/Schatten/UnitarilyInvariantNorm](UnitarilyInvariantNorm.md)

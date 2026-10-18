# Complex powers from a rank-one projection

## Abstract

Explicit complex powers of the identity plus the all-ones matrix.

**Definition 1.1 (The explicit matrix power).**

Lean statement: `D5/S3/Zeros/CriticalPoints/RankOneComplexPowers.H`

*Formalization.* `D5/S3/Zeros/CriticalPoints/RankOneComplexPowers.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural n and complex s, H(n,s) is I plus ((n+1)^s−1) times J/n, where the scalar power is exp(s log(n+1)). For n>0 these matrices multiply by adding exponents, H(n,0)=I, H(n,1)=I+J, and imaginary powers are unitary. The auxiliary positivePower function uses a real logarithm and agrees with Real.rpow on positive bases and real exponents.

**Theorem 1.2 (The column norm and the sharp coefficient).**

Lean statement: `D5/S3/Zeros/CriticalPoints/RankOneComplexPowers.column_norm_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/RankOneComplexPowers.column_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>0 and every real p, each column r_j of H(n,p/2), regarded as a complex Euclidean vector, has squared norm ((n+1)^p+n−1)/n. The inner products of distinct columns are ((n+1)^p−1)/n. For p>0 every pairwise inner product is nonzero, including diagonal pairs.

**Theorem 1.3 (The rank-one expansion of a diagonal sandwich).**

Lean statement: `D5/S3/Zeros/CriticalPoints/RankOneComplexPowers.sandwich_eq_sum_columns`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/RankOneComplexPowers.sandwich_eq_sum_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, real p and complex diagonal d, the matrix H(n,p/2) diag(d) H(n,p/2) is the sum over j of d_j times r_j r_j*. The columns are those of the same explicit Hermitian power. This expansion connects the interpolation matrix to the unitary rank-one trace estimate.

## References

- Truth anchor: `D5/S3/Zeros/CriticalPoints/RankOneComplexPowers.H`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/RankOneComplexPowers.column_norm_sq`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/RankOneComplexPowers.sandwich_eq_sum_columns`
- Dependency: [D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo](TangZhangOrderMinusTwo.md)

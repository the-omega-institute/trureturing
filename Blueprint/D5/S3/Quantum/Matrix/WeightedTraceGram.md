# Weighted trace Gram positivity

## Abstract

Weighted trace Gram positivity

**Theorem 1.1 (PSD weighted trace form).**

Lean statement: `D5/S3/Quantum/Matrix/WeightedTraceGram.weighted_traceGram_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/WeightedTraceGram.weighted_traceGram_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite index types n and m, complex n by n PSD L,R, arbitrary matrix words q indexed by m, and a real m by m PSD coefficient matrix M, the sum of M_ij Re Tr(L (q_i)* R q_j) is nonnegative. The proof uses a real square root of M and PSD congruence. Singular weights and non-Hermitian words are included.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/WeightedTraceGram.weighted_traceGram_nonneg`
- Dependency: [D5/S3/Quantum/Matrix/HsfQubitMixedCubic](HsfQubitMixedCubic.md)

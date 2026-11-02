# Four-path weighted equality remainder

## Abstract

For a four-dimensional unitary transport matrix, the Hilbert--Schmidt distance to a phased nonnegative diagonal is controlled by the squared trace defect.

**Theorem 1.1 (Weighted equality remainder).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathWeightedEqualityRemainder.weighted_equality_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathWeightedEqualityRemainder.weighted_equality_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For v : C^4 and U in U(4), let K = U diag(v), L be the sum of coordinate moduli, t be the trace modulus, and tau = L squared minus t squared. A unit phase lambda satisfies the Hilbert--Schmidt bound ‖K - lambda diag(|v|)‖ squared <= 2 tau.

The phase aligns the trace. Unitary entry bounds make the coordinate residuals nonnegative; the Frobenius expansion gives the weighted residual sum, and the trace triangle inequality supplies the final factorization.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FourPathWeightedEqualityRemainder.weighted_equality_remainder`
- Dependency: [D5/S3/Quantum/Foundation/HilbertSchmidtTraceStability](../Foundation/HilbertSchmidtTraceStability.md)
- Dependency: [D5/S3/Quantum/GNSMatrix](../GNSMatrix.md)

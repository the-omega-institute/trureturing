# Four-path weighted equality remainder

## Abstract

For a four-dimensional unitary transport matrix, the Hilbert--Schmidt distance to a phased nonnegative diagonal is controlled by the squared gap between the sum of coordinate moduli and the trace modulus.

**Lemma 10.1 (weighted equality remainder).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathWeightedEqualityRemainder.weighted_equality_remainder`.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathWeightedEqualityRemainder.weighted_equality_remainder` (`✓ std3`).

*Source.* `Meta/Digestion/backfill/quantum-reality-four-path-full-record-recovery-bound/residual-open/2ea4a553fb7295410c16bbb5071f46b687c4f12010f984d4fe1a207a47c9cca4.yaml`.

*Commentary.*

The theorem chooses a unit phase that aligns the trace with the nonnegative real axis. Entrywise unitary bounds make each residual nonnegative; the Frobenius expansion then reduces the matrix error to a weighted sum of these residuals. The trace triangle inequality and the factorization `(L+t)(L-t)=L²-t²` finish the estimate. Zero coordinates and the zero trace are included by the same argument.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FourPathWeightedEqualityRemainder.weighted_equality_remainder`
- Dependency: `D5/S3/Quantum/Foundation/HilbertSchmidtTraceStability.entryNormSq_eq_hs_sq`
- Dependency: `D5/S3/Quantum/GNSMatrix.frobenius_norm_sq_eq_trace`

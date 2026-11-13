# Decreasing error bounds for interval correlations

## Abstract

Decreasing error bounds for interval correlations

**Theorem 1.1 (antitone error envelope).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationEnvelope.antitone_error_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationEnvelope.antitone_error_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A uniformly negligible family of interval errors that is uniformly bounded on each bounded scale interval admits a nonnegative majorant, antitone on [2,infinity), tending to zero and bounding every error by the majorant times its moment scale. The majorant is the supremum of all subsequent normalized errors together with zero; local boundedness and eventual smallness ensure finiteness.

**Theorem 1.2 (correlation locally bounded).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationEnvelope.correlation_locally_bounded`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationEnvelope.correlation_locally_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural order and nonnegative window size M, the distinct correlations of an arbitrary real function on finite shift sets are locally uniformly bounded after division by (H log H)^(k/2) on H >= 2. On each bounded scale interval every shift tuple lies in one fixed finite product of bounded sets of natural numbers.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationEnvelope.antitone_error_envelope`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationEnvelope.correlation_locally_bounded`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs](FiniteSieveDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds](../FormalIntervalMomentBounds.md)

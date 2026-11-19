# Fourth-norm stability under perturbing both interval endpoints.

## Abstract

Fourth-norm stability under perturbing both interval endpoints.

**Theorem 1.1 (A uniform modulus of endpoint continuity).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveEndpointFourth.sieve_interval_endpoint_norm4_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveEndpointFourth.sieve_interval_endpoint_norm4_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume MSFinite and fix B>=1. There is C>=1 such that, for all sufficiently large real H and all positive Q with P<=B log H, ordered nonnegative intervals (a,b] and (c,d] whose corresponding endpoints differ by at most delta>=0 satisfy norm4(NI_(a,b]-NI_(c,d])<=C*(sqrt(delta)+H^(-1/4)). The constant and the eventual set of H are uniform in Q, delta and all four endpoints.

Write each interval as the difference of two prefixes. Their difference is the signed endpoint interval between b and d minus the signed endpoint interval between a and c. Each endpoint interval has length at most delta, and changing its sign preserves the fourth norm. The scalar bound after division by A_H bounds each piece by C0*(sqrt(delta)+H^(-1/4)). Minkowski adds the two pieces, giving C=2*C0. No disjointness assumption is needed.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveEndpointFourth.sieve_interval_endpoint_norm4_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveScalarFourth](SieveScalarFourth.md)

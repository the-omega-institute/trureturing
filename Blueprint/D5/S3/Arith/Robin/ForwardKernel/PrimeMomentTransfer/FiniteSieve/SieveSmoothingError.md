# Positive averages of translated interval indicators approximate finite sieve sums in the fourth norm.

## Abstract

Positive averages of translated interval indicators approximate finite sieve sums in the fourth norm.

**Theorem 1.1 (Uniform smoothing estimate).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothingError.sieve_smoothing_norm4_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothingError.sieve_smoothing_norm4_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume MSFinite and B>=1. There is C>=1 such that, for all sufficiently large real H, every modulus Q with P(Q)<=B log H, every 0<delta<=1, and all 0<=a<=b, the fourth norm of X_(a,b]/A_H-X_f/A_H is at most C*(sqrt(delta)+H^(-1/4)). The constant and the threshold are uniform in Q, delta, and the interval endpoints. The averaging estimate uses only nonnegativity, total mass one, the shift support, and the stated integrability properties of the normalized kernel.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothingError.sieve_smoothing_norm4_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveEndpointFourth](SieveEndpointFourth.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothKernel](SieveSmoothKernel.md)

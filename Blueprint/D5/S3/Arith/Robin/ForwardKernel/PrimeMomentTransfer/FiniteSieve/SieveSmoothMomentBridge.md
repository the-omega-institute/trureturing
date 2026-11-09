# The weighted moment identity

## Abstract

The weighted moment identity.

**Theorem 1.1 (The weighted moment identity).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothMomentBridge.sieve_weighted_moment_eq_raw`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothMomentBridge.sieve_weighted_moment_eq_raw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every order k, squarefree positive modulus Q, positive natural h and family of smooth real weights compactly supported in (0,infinity), the complex cast of the uniform finite-sieve product moment equals kuperbergRawMoment(Q,h,f). Compact support restricts every sample sum to a finite set. Positive support makes all negative integer samples vanish, identifying weightedExponentialSum with its natural sample sum. The centred Ramanujan expansion removes precisely the divisor q=1. Splitting the positive phase of x+d and distributing finite products gives one divisor and one reduced residue for each weight. The uniform residue average retains exactly the tuples whose rational total frequency is integral. The character sum Q cancels the average denominator Q, with no additional density factor or conjugation.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothMomentBridge.sieve_weighted_moment_eq_raw`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRamanujan](SieveRamanujan.md)

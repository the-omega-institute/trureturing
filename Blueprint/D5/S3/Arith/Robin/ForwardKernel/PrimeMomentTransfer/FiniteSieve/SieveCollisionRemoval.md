# Coincident-index removal for finite sieve moments

## Abstract

Coincident-index removal for finite sieve moments

**Theorem 1.1 (sieve collision removal).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCollisionRemoval.sieve_collision_removal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCollisionRemoval.sieve_collision_removal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M and B be at least one and let Q(H) = primorial(floor(((M+5)H)^10)). Suppose that, for all sufficiently large H, its density ratio is at most B log H, and all distinct two-index moments of interval indicators in [0,M] have absolute value at most KH log H. Assume also the uniform third interval moment and fourth interval pairing-defect estimates of FiniteSieveIntervals. Then the distinct third-index moments are o((H log H)^(3/2)), and the distinct fourth-index moments minus their three products of distinct two-index moments are o((H log H)^2), uniformly in the interval endpoints. The cubic collision error is bounded by a constant times H(log H)^2. The fourth quadratic and diagonal errors are bounded by a constant times H(log H)^3. Its six repeated-pair terms use the third-order conclusion on clamped intersections. After normalization the errors are controlled by sqrt(log H/H) and log H/H.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCollisionRemoval.sieve_collision_removal`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs](FiniteSieveDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds](../FormalIntervalMomentBounds.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra](../NormalizationAlgebra.md)

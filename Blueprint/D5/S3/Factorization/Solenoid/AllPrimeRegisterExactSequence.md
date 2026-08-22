# All-Prime Register Exact Sequence

## Abstract

The all-prime register is exact with a prime-adic hidden kernel.

**Theorem 1.1 (The all-prime register has the full prime-adic kernel).**

$$0 \to \prod_{p \text{prime}} \mathbb{Z}_{p} \to \Sigma \to \mathbb{T} \to 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Solenoid/AllPrimeRegisterExactSequence.all_prime_register_short_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the register containing every prime. Its hidden fiber is the product of one prime-adic integer ring for each prime, and its visible coordinate is a point on the circle. The theorem states injectivity of the hidden-fiber inclusion, exactness at the universal solenoid, surjectivity of the visible projection, and bijectivity of the kernel classification.

This is the source-enumerated all-prime exact-sequence clause. It does not assert an arbitrary-prime-set construction or identify the universal solenoid with a separately defined rational dual.

The repository already proves the exactness, surjectivity, and kernel classification in universal_solenoid_profinite_exact. The present theorem applies that exact result and records the injectivity of the canonical subtype inclusion explicitly.

## References

- Truth anchor: `D5/S3/Factorization/Solenoid/AllPrimeRegisterExactSequence.all_prime_register_short_exact`
- Dependency: [D5/S3/Factorization/SolenoidProfiniteKernel](../SolenoidProfiniteKernel.md)

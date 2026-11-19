# Stability of finite sieve products under fourth norm perturbations.

## Abstract

Stability of finite sieve products under fourth norm perturbations.

**Theorem 1.1 (Normalized product replacement).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveProductStability.sieve_product_moment_replacement`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveProductStability.sieve_product_moment_replacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two collections of k factors with fourth norms at most K and factorwise difference norms at most D, the absolute difference of their expected products is bounded by k D K^{k−1}, for 1 ≤ k ≤ 4.

**Theorem 1.2 (Wick pairing replacement).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveProductStability.sieve_wick_pairing_replacement`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveProductStability.sieve_wick_pairing_replacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For four factors satisfying the same K and D bounds, the difference between the sums of the three Wick pairing products is at most twelve times D times K cubed. Each covariance replacement costs at most two D K, and each covariance has size at most K squared.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveProductStability.sieve_product_moment_replacement`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveProductStability.sieve_wick_pairing_replacement`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FiniteProductMomentBounds](../../FourthTransfer/FiniteProductMomentBounds.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability](SieveFiniteProbability.md)

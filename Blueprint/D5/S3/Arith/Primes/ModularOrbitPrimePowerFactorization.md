# Exact orbit laws from canonical prime-power factors

## Abstract

The prime-power rules at the canonical factorization determine the complete finite orbit at each positive modulus.

**Theorem 1.1 (Canonical exact collision law at every positive modulus).**

Lean statement: `D5/S3/Arith/Primes/ModularOrbitPrimePowerFactorization.canonical_modulus_collision`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ModularOrbitPrimePowerFactorization.canonical_modulus_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use each support prime at its exact exponent in the modulus. The prime powers are pairwise coprime, and their product is the modulus. The result also covers modulus one via the empty list.

**Theorem 1.2 (Exact cardinality of the residue image at every positive modulus).**

Lean statement: `D5/S3/Arith/Primes/ModularOrbitPrimePowerFactorization.canonical_modulus_residue_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ModularOrbitPrimePowerFactorization.canonical_modulus_residue_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cardinality is exactly the maximum prime-power transient plus the least common multiple of the prime-power periods.

## References

- Truth anchor: `D5/S3/Arith/Primes/ModularOrbitPrimePowerFactorization.canonical_modulus_collision`
- Truth anchor: `D5/S3/Arith/Primes/ModularOrbitPrimePowerFactorization.canonical_modulus_residue_count`
- Dependency: [D5/S3/Arith/Primes/ModularOrbitTransientComposition](ModularOrbitTransientComposition.md)

# Combining modular orbit transients and periods

## Abstract

Exact local modular transients and periods compose under the Chinese remainder constraint.

**Theorem 1.1 (Exact collision law for pairwise coprime factors).**

Lean statement: `D5/S3/Arith/Primes/ModularOrbitTransientComposition.exact_product_sequence`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ModularOrbitTransientComposition.exact_product_sequence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two distinct indices collide modulo the product exactly when the earlier index is beyond every local transient and their lag is divisible by every local period. This combines transients by maximum and periods by least common multiple.

**Theorem 1.2 (Sharp onset and all positive shifts).**

Lean statement: `D5/S3/Arith/Primes/ModularOrbitTransientComposition.exact_tail_period`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ModularOrbitTransientComposition.exact_tail_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive shift preserves every reading from a chosen starting index if and only if that index is beyond the transient and the shift is a multiple of the period.

**Theorem 1.3 (The full residue image has transient plus period elements).**

Lean statement: `D5/S3/Arith/Primes/ModularOrbitTransientComposition.exact_residue_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ModularOrbitTransientComposition.exact_residue_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite prefix consisting of the whole transient and one complete period represents all residues exactly once. The formal proof gives a bijection, not just an upper bound.

## References

- Truth anchor: `D5/S3/Arith/Primes/ModularOrbitTransientComposition.exact_product_sequence`
- Truth anchor: `D5/S3/Arith/Primes/ModularOrbitTransientComposition.exact_residue_count`
- Truth anchor: `D5/S3/Arith/Primes/ModularOrbitTransientComposition.exact_tail_period`

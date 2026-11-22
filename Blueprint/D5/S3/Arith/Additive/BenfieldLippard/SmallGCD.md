# The gcd of small shifted powers

## Abstract

For the odd-exponent estimate, the shifts from the first floor(p/3) bases have gcd one.

**Definition 1.1 (Shifted powers with bounded bases).**

Lean statement: `D5/S3/Arith/Additive/BenfieldLippard/SmallGCD.smallGenerators`

*Formalization.* `D5/S3/Arith/Additive/BenfieldLippard/SmallGCD.smallGenerators` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brennan Benfield, Oliver Lippard (2025). *Integers that are not the sum of positive powers*. URL: <https://arxiv.org/abs/2404.08193v2>.

*Commentary.*

For positive bases at most m, collect the shifted powers a^k−1.

**Theorem 1.2 (The gcd of small shifted powers).**

Lean statement: `D5/S3/Arith/Additive/BenfieldLippard/SmallGCD.small_gcd`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/BenfieldLippard/SmallGCD.small_gcd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Brennan Benfield, Oliver Lippard (2025). *Integers that are not the sum of positive powers*. URL: <https://arxiv.org/abs/2404.08193v2>.

*Commentary.*

A prime divisor common to the shifts would force all the small bases to be kth roots of unity. For a modulus up to the square of the base cutoff, an integer quotient and remainder force 1 = −1. Above that square, the products of powers of two and small odd bases give more distinct roots than the degree.

## References

- Truth anchor: `D5/S3/Arith/Additive/BenfieldLippard/SmallGCD.smallGenerators`
- Truth anchor: `D5/S3/Arith/Additive/BenfieldLippard/SmallGCD.small_gcd`

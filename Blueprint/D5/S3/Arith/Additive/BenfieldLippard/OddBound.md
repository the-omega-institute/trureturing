# The upper bound at odd exponents

## Abstract

Small shifted powers give a conductor bound that controls the number of gaps for the neighboring odd exponents.

**Theorem 1.1 (An upper bound from small generators).**

Lean statement: `D5/S3/Arith/Additive/BenfieldLippard/OddBound.odd_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/BenfieldLippard/OddBound.odd_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Brennan Benfield, Oliver Lippard (2025). *Integers that are not the sum of positive powers*. URL: <https://arxiv.org/abs/2404.08193v2>.

*Commentary.*

Let p ≥ 193 and take a positive odd exponent k ≤ p. The shifted powers from bases at most ⌊p/3⌋ have gcd one. Modulo 2^k−1, every residue has a representative of weight at most (2^k−2)(⌊p/3⌋^k−1). Adding copies of 2^k−1 covers all integers beyond this conductor bound. The resulting comparison is 2|B(k)| < p^(p−1).

## References

- Truth anchor: `D5/S3/Arith/Additive/BenfieldLippard/OddBound.odd_upper`
- Dependency: [D5/S3/Arith/Additive/BenfieldLippard/Conductor](Conductor.md)
- Dependency: [D5/S3/Arith/Additive/BenfieldLippard/SmallGCD](SmallGCD.md)
- Dependency: [D5/S3/Arith/Additive/BenfieldLippard/Stabilization](Stabilization.md)

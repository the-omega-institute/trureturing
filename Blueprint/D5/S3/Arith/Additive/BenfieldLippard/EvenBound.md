# The lower bound at prime-minus-one exponents

## Abstract

Fermat divisibility produces many gaps at exponents one less than a prime.

**Theorem 1.1 (A Fermat lower bound).**

Lean statement: `D5/S3/Arith/Additive/BenfieldLippard/EvenBound.even_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/BenfieldLippard/EvenBound.even_lower` (`✓ std3`). ∎

*Citation.* Brennan Benfield, Oliver Lippard (2025). *Integers that are not the sum of positive powers*. URL: <https://arxiv.org/abs/2404.08193v2>.

*Commentary.*

For a prime p at least four, any representable offset below p^(p−1)−1 uses bases smaller than p. Fermat's little theorem makes each shifted power divisible by p. Counting the positive nonmultiples of p in the interval gives p^(p−1) ≤ 2|B(p−1)|. The lower-bound mechanism is that of Benfield and Lippard's Theorem 10.7.

## References

- Truth anchor: `D5/S3/Arith/Additive/BenfieldLippard/EvenBound.even_lower`
- Dependency: [D5/S3/Arith/Additive/BenfieldLippard/Stabilization](Stabilization.md)

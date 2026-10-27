# OEIS A361035: parity of a quartic factorial quotient

## Abstract

Bala's OEIS A361035 parity characterization.

**Definition 1.1 (a).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{Nat}.\operatorname{div}\left(9979200 \cdot \operatorname{Nat}.\operatorname{factorial}\left(4 \cdot n\right), \operatorname{Nat}.\operatorname{factorial}\left(n\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(n + 3\right)^{3}\right)$$

*Formalization.* `D5/S3/Arith/FactorialRatio/BalaA361035Parity.a` (`✓ std3`).

*Citation.* Peter Bala (2023). *OEIS A361034 and A361035: parity of quartic factorial quotients*. URL: <https://oeis.org/A361034>.

*Commentary.*

OEIS A361035, NAME (unpaginated): "a(n) = 9979200 * (4*n)!/(n!*(n+3)!^3)." The index n is a natural number, including zero. Nat.div denotes natural-number division; the factorial denominator divides the numerator.

**Definition 1.2 (claim).**

$$\operatorname{claim} = (\forall n \in \mathbb{N},\; \operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \Leftrightarrow \left(\exists k \in \mathbb{N},\; 2 \le k \land n = 2^{k} - 3\right))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/BalaA361035Parity.claim` (`✓ std3`).

*Citation.* Peter Bala (2023). *OEIS A361034 and A361035: parity of quartic factorial quotients*. URL: <https://oeis.org/A361034>.

*Commentary.*

OEIS A361035, COMMENTS (unpaginated): "Conjecture: a(n) is odd iff n = 2^k - 3 for some k >= 2." Both n and k range over the natural numbers. The lower bound on k makes the subtraction exact.

**Theorem 1.3 (result).**

$$\forall n \in \mathbb{N},\; \operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \Leftrightarrow \left(\exists k \in \mathbb{N},\; 2 \le k \land n = 2^{k} - 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/BalaA361035Parity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2023). *OEIS A361034 and A361035: parity of quartic factorial quotients*. URL: <https://oeis.org/A361034>.

*Commentary.*

The factorial quotient is odd exactly at the stated indices. Its exponent of 2 is three times the binary digit sum of n + 3, less three; this vanishes exactly when n + 3 is a power of two.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA361035Parity.a`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA361035Parity.claim`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA361035Parity.result`
- Dependency: [D5/S3/Arith/FactorialRatio/BalaA361034Parity](BalaA361034Parity.md)

# OEIS A361034: parity of a quartic factorial quotient

## Abstract

Bala's OEIS A361034 parity characterization.

**Theorem 1.1 (quotient_odd).**

$$\forall C \in \mathbb{N},\; \forall j \in \mathbb{N},\; \forall n \in \mathbb{N},\; \left(0 < C \land \left(0 < j \land \left(8 \cdot \operatorname{Nat}.\operatorname{factorial}\left(j\right) \cdot C = \operatorname{Nat}.\operatorname{factorial}\left(4 \cdot j\right) \land \operatorname{Nat}.\operatorname{factorization}\left(C, 2\right) = 3 \cdot j - 3\right)\right)\right) \Rightarrow \left(\operatorname{Odd}\left(\operatorname{Nat}.\operatorname{div}\left(C \cdot \operatorname{Nat}.\operatorname{factorial}\left(4 \cdot n\right), \operatorname{Nat}.\operatorname{factorial}\left(n\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(n + j\right)^{3}\right)\right) \Leftrightarrow \left(\exists k \in \mathbb{N},\; n + j = 2^{k}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/BalaA361034Parity.quotient_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2023). *OEIS A361034 and A361035: parity of quartic factorial quotients*. URL: <https://oeis.org/A361034>.

*Commentary.*

For positive natural numbers C and j, when 8 j! C = (4j)! and the exponent of 2 in C is 3j - 3, the factorial quotient is an integer and is odd exactly when n + j is a power of two. The binary digit sum determines the exponent of 2 in the quotient.

**Definition 1.2 (a).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{Nat}.\operatorname{div}\left(2520 \cdot \operatorname{Nat}.\operatorname{factorial}\left(4 \cdot n\right), \operatorname{Nat}.\operatorname{factorial}\left(n\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(n + 2\right)^{3}\right)$$

*Formalization.* `D5/S3/Arith/FactorialRatio/BalaA361034Parity.a` (`✓ std3`).

*Citation.* Peter Bala (2023). *OEIS A361034 and A361035: parity of quartic factorial quotients*. URL: <https://oeis.org/A361034>.

*Commentary.*

OEIS A361034, NAME (unpaginated): "a(n) = 2520*(4*n)!/(n!*(n+2)!^3)." The index n is a natural number, including zero. Nat.div denotes natural-number division; the factorial denominator divides the numerator.

**Definition 1.3 (claim).**

$$\operatorname{claim} = (\forall n \in \mathbb{N},\; \operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \Leftrightarrow \left(\exists k \in \mathbb{N},\; 1 \le k \land n = 2^{k} - 2\right))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/BalaA361034Parity.claim` (`✓ std3`).

*Citation.* Peter Bala (2023). *OEIS A361034 and A361035: parity of quartic factorial quotients*. URL: <https://oeis.org/A361034>.

*Commentary.*

OEIS A361034, COMMENTS (unpaginated): "Conjecture: a(n) is odd iff n = 2^k - 2 for some k >= 1." Both n and k range over the natural numbers. The lower bound on k makes the subtraction exact.

**Theorem 1.4 (result).**

$$\forall n \in \mathbb{N},\; \operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \Leftrightarrow \left(\exists k \in \mathbb{N},\; 1 \le k \land n = 2^{k} - 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/BalaA361034Parity.result` (`✓ std3`). ∎

*Resolves.* `Problems/bala3610-parity` (proved) by `D5/S3/Arith/FactorialRatio/BalaA361034Parity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bala3610-parity","declaration_gid":"D5/S3/Arith/FactorialRatio/BalaA361034Parity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2023). *OEIS A361034 and A361035: parity of quartic factorial quotients*. URL: <https://oeis.org/A361034>.

*Commentary.*

The factorial quotient is odd exactly at the stated indices. Its exponent of 2 is three times the binary digit sum of n + 2, less three; this vanishes exactly when n + 2 is a power of two.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA361034Parity.a`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA361034Parity.claim`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA361034Parity.quotient_odd`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA361034Parity.result`
- Dependency: [D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral](OeisA347854BalaHalfIndexIntegral.md)

# Jordan-Cototient Record Limit at Zero

## Abstract

For each positive natural input, eventual strict Jordan-cototient record membership at sufficiently small positive parameters is characterized by the number of distinct prime factors, with three exceptional values.

**Theorem 1.1 (The eventual record set near zero).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left((\exists epsilon \in \mathbb{R},\; 0 < epsilon \land \left(\forall k \in \mathbb{R},\; 0 < k \Rightarrow \left(k < epsilon \Rightarrow \operatorname{StrictRecord}\left(k, n\right)\right)\right)) \Leftrightarrow (n \in \{1, 2, 4\} \lor 2 \le \operatorname{card}\left(\operatorname{primeFactors}\left(n\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/JordanCototientRecordLimitZero.a387335_eventual_record_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n >= 1, there is a positive real epsilon such that n is a strict Jordan-cototient record for every real parameter k with 0 < k < epsilon exactly when n is one, two, four, or has at least two distinct prime factors. Equivalently, after the three exceptional values, these eventual records are the non-prime-powers listed by OEIS A024619.

The threshold may depend on n. At parameter zero every input n > 1 has Jordan cototient one. Its right derivative is log(n) when n has at least two distinct prime factors, and log(p^(a-1)) when n=p^a. Strict derivative comparisons hold simultaneously for the finitely many positive predecessors of n.

For exclusion, an odd prime power p^a with a >= 2 loses to 2*p^(a-1), while 2^a with a >= 3 loses to 3*2^(a-2). Every prime greater than two ties with two. These comparisons prove the pointwise eventual characterization stated in the OEIS A387335 comment of Hal M. Switkay dated 2025-11-30.

## References

- Truth anchor: `D5/S3/Factorization/JordanCototientRecordLimitZero.a387335_eventual_record_iff`
- Dependency: [D5/S3/Factorization/JordanCototientRecordLimitInfinity](JordanCototientRecordLimitInfinity.md)

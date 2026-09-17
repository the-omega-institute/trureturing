# Ordowski's A306270 Semiprime Classification

## Abstract

Ordowski's semiprimes in A306270 have the prime factors prescribed by A190275.

All variables range over the natural numbers N, including zero. The letter k denotes a sequence candidate, p and q denote prime factors with p at most q, and b denotes an arbitrary residue representative. Prime(x) means that x is prime, gcd is the natural greatest common divisor, mem is membership in A306270, and congruence is taken modulo the displayed natural modulus. Powers, products, order, and subtraction are natural-number operations, so subtraction is truncated at zero. The scope is exactly Ordowski's Conjecture sentence for every semiprime k greater than four. The classification proof is content-bearing: it turns the universal congruence into a Carmichael exponent divisibility and follows the prime-square divisor chain to the factor equality.

**Definition 1.1 (Membership in A306270).**

$$\forall k \in \mathbb{N},\; (\operatorname{mem}\left(k\right)) \Leftrightarrow ((\neg \operatorname{Prime}\left(k\right)) \land \left((1 < k) \land (\forall b \in \mathbb{N},\; (\operatorname{gcd}\left(b, k\right) = 1) \Rightarrow (b^{k \cdot \left(k - 1\right)} \equiv 1 (\operatorname{mod} k^{2})))\right))$$

*Formalization.* `D5/S3/Arith/Congruence/OrdowskiSemiprimeCarmichaelSquareClassification.mem` (`✓ std3`).

*Citation.* Thomas Ordowski (2020). *OEIS A306270, composite k with b^(k(k-1)) = 1 mod k^2 for all b coprime to k, with the conjecture that its semiprimes > 4 are the p(p^2-p+1) of A190275*. URL: <https://oeis.org/A306270>.

*Commentary.*

A natural number k belongs to A306270 when it is composite and greater than one, and every natural b coprime to k has b^(k(k-1)) congruent to one modulo k^2.

**Theorem 1.2 (Ordowski's semiprime classification).**

$$\forall p \in \mathbb{N}, q \in \mathbb{N},\; (\operatorname{Prime}\left(p\right)) \Rightarrow ((\operatorname{Prime}\left(q\right)) \Rightarrow ((p \le q) \Rightarrow ((4 < p \cdot q) \Rightarrow ((\operatorname{mem}\left(p \cdot q\right)) \Rightarrow (q = p^{2} - p + 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/OrdowskiSemiprimeCarmichaelSquareClassification.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a306270-ordowski-semiprime-carmichael-square-classification` (proved) by `D5/S3/Arith/Congruence/OrdowskiSemiprimeCarmichaelSquareClassification.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a306270-ordowski-semiprime-carmichael-square-classification","declaration_gid":"D5/S3/Arith/Congruence/OrdowskiSemiprimeCarmichaelSquareClassification.result","resolution_kind":"proved"} -->

*Citation.* Thomas Ordowski (2020). *OEIS A306270, composite k with b^(k(k-1)) = 1 mod k^2 for all b coprime to k, with the conjecture that its semiprimes > 4 are the p(p^2-p+1) of A190275*. URL: <https://oeis.org/A306270>.

*Commentary.*

If k=pq is greater than four, p and q are prime, p is at most q, and k belongs to A306270, then q=p^2-p+1. Consequently k has the form p(p^2-p+1) from A190275. The subtraction in the displayed equality is natural subtraction.

## References

- Truth anchor: `D5/S3/Arith/Congruence/OrdowskiSemiprimeCarmichaelSquareClassification.mem`
- Truth anchor: `D5/S3/Arith/Congruence/OrdowskiSemiprimeCarmichaelSquareClassification.result`

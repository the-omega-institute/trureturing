# Rotondo's Lucas-Carmichael criterion

## Abstract

Rotondo's factorization conditions imply the Lucas-Carmichael divisibility criterion.

All variables range over the natural numbers N. The letters p, q, and r denote distinct odd primes, k is their product, and d is the greatest common divisor of p+1, q+1, and r+1. The positive factors a, b, and c satisfy p+1=ad, q+1=bd, and r+1=cd. A Lucas-Carmichael number is squarefree and composite, is greater than one, and has s+1 dividing k+1 for every prime divisor s of k.

**Definition 1.1 (Lucas-Carmichael numbers).**

$$\forall k \in \mathbb{N},\; (\operatorname{IsLucasCarmichael}\left(k\right)) \Leftrightarrow ((\operatorname{Squarefree}\left(k\right)) \land \left((\neg \operatorname{Prime}\left(k\right)) \land \left((1 < k) \land (\forall s \in \mathbb{N},\; (\operatorname{Prime}\left(s\right)) \Rightarrow ((s \mid k) \Rightarrow (s + 1 \mid k + 1)))\right)\right))$$

*Formalization.* `D5/S3/Arith/Congruence/RotondoLucasCarmichaelCriterion.IsLucasCarmichael` (`✓ std3`).

*Citation.* Davide Rotondo (2020). *OEIS A006972, Lucas-Carmichael numbers, with Rotondo's sufficient condition for three distinct odd prime factors*. URL: <https://oeis.org/A006972>.

*Commentary.*

A natural number k is Lucas-Carmichael when it is squarefree, composite, greater than one, and every prime divisor s satisfies s+1 divides k+1.

**Theorem 1.2 (Rotondo's sufficient condition).**

$$\forall a \in \mathbb{N}, b \in \mathbb{N}, c \in \mathbb{N}, d \in \mathbb{N}, p \in \mathbb{N}, q \in \mathbb{N}, r \in \mathbb{N}, k \in \mathbb{N},\; (0 < a) \Rightarrow ((0 < b) \Rightarrow ((0 < c) \Rightarrow ((0 < d) \Rightarrow ((0 < p) \Rightarrow ((0 < q) \Rightarrow ((0 < r) \Rightarrow ((0 < k) \Rightarrow ((k = p \cdot q \cdot r) \Rightarrow ((\operatorname{Prime}\left(p\right)) \Rightarrow ((\operatorname{Prime}\left(q\right)) \Rightarrow ((\operatorname{Prime}\left(r\right)) \Rightarrow ((\operatorname{Odd}\left(p\right)) \Rightarrow ((\operatorname{Odd}\left(q\right)) \Rightarrow ((\operatorname{Odd}\left(r\right)) \Rightarrow ((p \ne q) \Rightarrow ((p \ne r) \Rightarrow ((q \ne r) \Rightarrow ((p + 1 = a \cdot d) \Rightarrow ((q + 1 = b \cdot d) \Rightarrow ((r + 1 = c \cdot d) \Rightarrow ((d = \operatorname{gcd}\left(p + 1, \operatorname{gcd}\left(q + 1, r + 1\right)\right)) \Rightarrow ((a \cdot b \cdot c \cdot d \mid k + 1) \Rightarrow (\operatorname{IsLucasCarmichael}\left(k\right))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/RotondoLucasCarmichaelCriterion.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a006972-rotondo-lucas-carmichael-sufficient-condition` (proved) by `D5/S3/Arith/Congruence/RotondoLucasCarmichaelCriterion.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a006972-rotondo-lucas-carmichael-sufficient-condition","declaration_gid":"D5/S3/Arith/Congruence/RotondoLucasCarmichaelCriterion.result","resolution_kind":"proved"} -->

*Citation.* Davide Rotondo (2020). *OEIS A006972, Lucas-Carmichael numbers, with Rotondo's sufficient condition for three distinct odd prime factors*. URL: <https://oeis.org/A006972>.

*Commentary.*

For positive a, b, c, d, p, q, r, and k satisfying the displayed product, prime, oddness, distinctness, factor, greatest-common-divisor, and divisibility hypotheses, k is Lucas-Carmichael. Distinct primality makes pqr squarefree and composite. Every prime divisor of pqr is one of p, q, and r; its successor therefore divides abcd and hence k+1.

## References

- Truth anchor: `D5/S3/Arith/Congruence/RotondoLucasCarmichaelCriterion.IsLucasCarmichael`
- Truth anchor: `D5/S3/Arith/Congruence/RotondoLucasCarmichaelCriterion.result`

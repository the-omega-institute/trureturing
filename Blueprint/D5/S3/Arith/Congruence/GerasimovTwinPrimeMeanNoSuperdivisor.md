# The A254748 Twin-Prime Mean Conjecture

## Abstract

Twin-prime pair averages have no superdivisor.

**Definition 1.1 (The A247477 superdivisor predicate).**

$$\forall n \in {\mathbb N}, k \in {\mathbb N},\; IsSuperdivisor\left(n, k\right) \Leftrightarrow (n / k + n \mid (n / k)^{n / k} + n \land \left(n / k + n \mid (n / k)^{n} + n / k \land n / k + n \mid n^{n / k} + n / k\right))$$

*Formalization.* `D5/S3/Arith/Congruence/GerasimovTwinPrimeMeanNoSuperdivisor.IsSuperdivisor` (`✓ std3`).

*Citation.* Juri-Stepan Gerasimov (2015). *OEIS A254748, Numbers without superdivisors*. URL: <https://oeis.org/A254748>.

*Commentary.*

For natural n and k, the three displayed divisibility conditions define a superdivisor. The slash is natural-number division, and it agrees with the exact quotient when k divides n.

**Theorem 1.2 (The twin-prime mean theorem).**

$$\forall p \in {\mathbb N},\; Prime\left(p\right) \Rightarrow \left(Prime\left(p + 2\right) \Rightarrow \left(\forall k \in {\mathbb N},\; 1 \le k \Rightarrow \left(k \mid p + 1 \Rightarrow \left(\neg IsSuperdivisor\left(p + 1, k\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/GerasimovTwinPrimeMeanNoSuperdivisor.gerasimov_a254748` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a254748-twin-prime-mean-no-superdivisor` (proved) by `D5/S3/Arith/Congruence/GerasimovTwinPrimeMeanNoSuperdivisor.gerasimov_a254748`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a254748-twin-prime-mean-no-superdivisor","declaration_gid":"D5/S3/Arith/Congruence/GerasimovTwinPrimeMeanNoSuperdivisor.gerasimov_a254748","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

For twin primes p and p+2, every positive divisor k of p+1 fails the superdivisor predicate. The proof uses the multiplicative order in ZMod (k+1), through the stronger statement for an even n at least 4 whose predecessor is prime.

## References

- Truth anchor: `D5/S3/Arith/Congruence/GerasimovTwinPrimeMeanNoSuperdivisor.IsSuperdivisor`
- Truth anchor: `D5/S3/Arith/Congruence/GerasimovTwinPrimeMeanNoSuperdivisor.gerasimov_a254748`

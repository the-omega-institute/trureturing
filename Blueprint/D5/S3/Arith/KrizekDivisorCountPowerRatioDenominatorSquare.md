# The OEIS A302975 Denominator-Square Conjecture

## Abstract

Every reduced denominator in OEIS A302975 is a square.

**Definition 1.1 (The reduced denominator of the divisor-count ratio).**

$$\forall n \in \mathbb{N}, \operatorname{D}\left(n\right) = \operatorname{den}\left(\frac{{(\lvert\operatorname{divisors}\left(n\right)\rvert : \mathbb{Q})}^{n}}{{(n : \mathbb{Q})}^{\lvert\operatorname{divisors}\left(n\right)\rvert}}\right)$$

*Formalization.* `D5/S3/Arith/KrizekDivisorCountPowerRatioDenominatorSquare.D` (`✓ std3`).

*Citation.* Jaroslav Krizek (2018). *OEIS A302975, a(n) = denominator of tau(n)^n / n^tau(n)*. URL: <https://oeis.org/A302975>.

*Commentary.*

For each natural n, tau(n) is the cardinality of the positive divisors of n. The function D is the reduced denominator of the rational ratio tau(n)^n / n^tau(n); its value D(0)=1 is a totalization artefact, not part of the source claim.

**Theorem 1.2 (Every positive A302975 denominator is a square).**

$$\forall n \in \mathbb{N}, 1 \le n \Rightarrow \operatorname{IsSquare}\left(\operatorname{D}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/KrizekDivisorCountPowerRatioDenominatorSquare.krizek_a302975` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a302975-divisor-count-power-ratio-denominator-square` (proved) by `D5/S3/Arith/KrizekDivisorCountPowerRatioDenominatorSquare.krizek_a302975`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a302975-divisor-count-power-ratio-denominator-square","declaration_gid":"D5/S3/Arith/KrizekDivisorCountPowerRatioDenominatorSquare.krizek_a302975","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

For every positive n, the denominator has even prime valuations. The valuation formula for the reduced ratio splits according to the parity of n and the divisor count; the odd case is forced to have zero valuation whenever a prime divides the divisor count. Reconstructing from the even valuations gives a square.

## References

- Truth anchor: `D5/S3/Arith/KrizekDivisorCountPowerRatioDenominatorSquare.D`
- Truth anchor: `D5/S3/Arith/KrizekDivisorCountPowerRatioDenominatorSquare.krizek_a302975`

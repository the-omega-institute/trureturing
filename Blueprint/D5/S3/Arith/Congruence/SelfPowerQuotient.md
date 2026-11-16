# The exact self-power quotient

## Abstract

For every natural index n, the self-power numerator is divisible by (n+1)^2.

**Definition 1.1 (The source numerator).**

$$\forall n \in \mathbb{N},\; \operatorname{numerator}\left(n\right) = ((n: \mathbb{Z}))^{n+1}+(-1)^{n}$$

*Formalization.* `D5/S3/Arith/Congruence/SelfPowerQuotient.numerator` (`✓ std3`).

*Citation.* Mathew Englander (2020). *Comments on OEIS A081215*. URL: <https://oeis.org/A081215/a081215.pdf>.

*Commentary.*

Englander, definition on physical page 1: the natural index is cast into the integers before taking the power. The sign exponent is natural.

**Definition 1.2 (The shared sequence).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \frac{\operatorname{numerator}\left(n\right)}{((n: \mathbb{Z})+1)^{2}}$$

*Formalization.* `D5/S3/Arith/Congruence/SelfPowerQuotient.a` (`✓ std3`).

*Citation.* Mathew Englander (2020). *Comments on OEIS A081215*. URL: <https://oeis.org/A081215/a081215.pdf>.

*Commentary.*

The quotient uses integer Euclidean division. The exact quotient identity below proves that no truncation affects this value at any natural index, including zero. All three modules use this same definition.

**Definition 1.3 (An integrated geometric sum).**

$$\forall j \in \mathbb{N},\; \forall y \in \mathbb{Z},\; \operatorname{tail}\left(j, y\right) = \sum_{i<j} \sum_{r<i} (y)^{r}$$

*Formalization.* `D5/S3/Arith/Congruence/SelfPowerQuotient.tail` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathew Englander (2020). *Comments on OEIS A081215*. URL: <https://oeis.org/A081215/a081215.pdf>.

*Commentary.*

The auxiliary integer polynomial is the sum of the geometric sums with lengths from zero through j minus one; empty sums are zero. This is a proof device, not an additional source sequence.

**Theorem 1.4 (A division-free formula).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = (-1)^{n}*(1-\operatorname{tail}\left(n+1, -(n: \mathbb{Z})\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/SelfPowerQuotient.quotient_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathew Englander (2020). *Comments on OEIS A081215*. URL: <https://oeis.org/A081215/a081215.pdf>.

*Commentary.*

Multiplying each inner geometric sum by y minus one applies Mathlib geom_sum_mul directly. Summing gives T(j,y)*(y-1)=S(j,y)-j and then T(j,y)*(y-1)^2=y^j-1-j*(y-1). Substituting j=n+1 and y=-n and using the square of the sign gives the displayed integer formula.

**Theorem 1.5 (Exact integrality).**

$$\forall n \in \mathbb{N},\; ((n: \mathbb{Z})+1)^{2}*\operatorname{a}\left(n\right) = \operatorname{numerator}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/SelfPowerQuotient.exact_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathew Englander (2020). *Comments on OEIS A081215*. URL: <https://oeis.org/A081215/a081215.pdf>.

*Commentary.*

For every natural n, the positive nonzero denominator times the integer quotient equals the original numerator. Thus the original rational quotient is this integer, rather than an unverified truncated value. Natural indices above two are exactly the integer indices in XIV; positive k and n greater than k in XVII likewise imply a positive natural index.

## References

- Truth anchor: `D5/S3/Arith/Congruence/SelfPowerQuotient.a`
- Truth anchor: `D5/S3/Arith/Congruence/SelfPowerQuotient.exact_quotient`
- Truth anchor: `D5/S3/Arith/Congruence/SelfPowerQuotient.numerator`
- Truth anchor: `D5/S3/Arith/Congruence/SelfPowerQuotient.quotient_tail`
- Truth anchor: `D5/S3/Arith/Congruence/SelfPowerQuotient.tail`

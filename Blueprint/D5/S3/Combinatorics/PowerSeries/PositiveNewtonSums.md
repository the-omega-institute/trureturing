# Positive coefficients of the five-data Newton sums

## Abstract

Strict positive monomial coefficients give the rational shifted generating function and the positive-index recurrence for A301420.

All series have rational coefficients. Fin(5) is indexed by i = 0,1,2,3,4; its coordinate i has weight i+1. Positive sequence indices belong to N with zero excluded. X is the series variable, C embeds rational constants, and the inverse is the formal multiplicative inverse. The formal log is log(1+X); subst(p,f) substitutes p into f, and rescale(c,f) replaces X by cX.

**Definition 1.1 (Multiplicity vectors).**

$$Multiplicity = \operatorname{Fin}\left(5\right)\to\mathbb{N}$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.Multiplicity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gregory Gerard Wojnar (2018). *OEIS A301420: positive coefficients of five-data generalized Chebyshev polynomials*. URL: <https://oeis.org/A301420>.

*Commentary.*

A vector records one nonnegative multiplicity for each of the five distinct monomial variables.

**Definition 1.2 (Factor count).**

$$\forall m \in Multiplicity,\; \operatorname{count}\left(m\right) = \sum_{i\in\operatorname{Fin}\left(5\right)}(\operatorname{m}\left(i\right))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.count` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gregory Gerard Wojnar (2018). *OEIS A301420: positive coefficients of five-data generalized Chebyshev polynomials*. URL: <https://oeis.org/A301420>.

*Commentary.*

The total number r of factors is the unweighted sum of the five multiplicities.

**Definition 1.3 (Weighted degree).**

$$\forall m \in Multiplicity,\; \operatorname{degree}\left(m\right) = \sum_{i\in\operatorname{Fin}\left(5\right)}(\left(i + 1\right) \cdot \operatorname{m}\left(i\right))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.degree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gregory Gerard Wojnar (2018). *OEIS A301420: positive coefficients of five-data generalized Chebyshev polynomials*. URL: <https://oeis.org/A301420>.

*Commentary.*

The five weights are one through five. The factor count is at most this weighted degree.

**Definition 1.4 (Monomials of a fixed degree).**

$$\forall k \in \mathbb{N},\; \forall m \in Multiplicity,\; m\in\operatorname{multiplicities}\left(k\right)\iff\operatorname{degree}\left(m\right) = k$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.multiplicities` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gregory Gerard Wojnar (2018). *OEIS A301420: positive coefficients of five-data generalized Chebyshev polynomials*. URL: <https://oeis.org/A301420>.

*Commentary.*

The finite set is the union over r from zero through k of the r-factor antidiagonals, filtered by weighted degree k. Membership is equivalent to degree(m)=k, so every multiplicity vector occurs once.

**Definition 1.5 (The literal Girard-Waring coefficient).**

$$\forall k \in (\mathbb{N})^{+},\; \forall m \in Multiplicity,\; \operatorname{literalCoefficient}\left(k, m\right) = \frac{k}{5 \cdot \operatorname{count}\left(m\right)} \cdot \frac{\operatorname{factorial}\left(\operatorname{count}\left(m\right)\right)}{\prod_{i\in\operatorname{Fin}\left(5\right)}(\operatorname{factorial}\left(\operatorname{m}\left(i\right)\right))} \cdot \prod_{i\in\operatorname{Fin}\left(5\right)}((\operatorname{choose}\left(5, i + 1\right))^{\operatorname{m}\left(i\right)}) \cdot (-1)^{k + \operatorname{count}\left(m\right)}$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.literalCoefficient` (`✓ std3`).

*Citation.* Gregory Gerard Wojnar (2018). *OEIS A301420: positive coefficients of five-data generalized Chebyshev polynomials*. URL: <https://oeis.org/A301420>.

*Commentary.*

Equation (2) of Wojnar, Wojnar and Brin, arXiv:1706.08381v2, pp. 3-4, gives this normalized five-data coefficient. For a vector of degree k its factor count is positive. The coefficient is attached to a monomial before data values are substituted.

**Definition 1.6 (The unsigned weight).**

$$\forall k \in (\mathbb{N})^{+},\; \forall m \in Multiplicity,\; \operatorname{unsignedCoefficient}\left(k, m\right) = \frac{k}{5 \cdot \operatorname{count}\left(m\right)} \cdot \frac{\operatorname{factorial}\left(\operatorname{count}\left(m\right)\right)}{\prod_{i\in\operatorname{Fin}\left(5\right)}(\operatorname{factorial}\left(\operatorname{m}\left(i\right)\right))} \cdot \prod_{i\in\operatorname{Fin}\left(5\right)}((\operatorname{choose}\left(5, i + 1\right))^{\operatorname{m}\left(i\right)})$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.unsignedCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gregory Gerard Wojnar (2018). *OEIS A301420: positive coefficients of five-data generalized Chebyshev polynomials*. URL: <https://oeis.org/A301420>.

*Commentary.*

Removing only the parity sign gives the absolute value of the literal coefficient.

**Definition 1.7 (The sequence on positive indices).**

$$\forall k \in (\mathbb{N})^{+},\; \operatorname{positiveCoefficient}\left(k\right) = \sum_{m\in\operatorname{multiplicities}\left(k\right)}(\operatorname{positivePart}\left(\operatorname{literalCoefficient}\left(k, m\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.positiveCoefficient` (`✓ std3`).

*Citation.* Gregory Gerard Wojnar (2018). *OEIS A301420: positive coefficients of five-data generalized Chebyshev polynomials*. URL: <https://oeis.org/A301420>.

*Commentary.*

positivePart(c) means c if c>0 and zero otherwise. This is the strict positive coefficient sum in the NAME and COMMENTS of OEIS A301420. Each distinct monomial is filtered separately. No index-zero sequence value is defined.

**Definition 1.8 (The shifted series).**

$$\forall n \in \mathbb{N},\; \operatorname{coeff}\left(n, positiveSeries\right) = \operatorname{positiveCoefficient}\left(n + 1\right)$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.positiveSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gregory Gerard Wojnar (2018). *OEIS A301420: positive coefficients of five-data generalized Chebyshev polynomials*. URL: <https://oeis.org/A301420>.

*Commentary.*

The coefficient at degree n is the sequence value at n+1. This shift interprets the entry's offset one.

**Definition 1.9 (The data polynomial).**

$$dataSeries = \sum_{i\in\operatorname{Fin}\left(5\right)}(\operatorname{monomial}\left(i + 1, \operatorname{choose}\left(5, i + 1\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.dataSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gregory Gerard Wojnar (2018). *OEIS A301420: positive coefficients of five-data generalized Chebyshev polynomials*. URL: <https://oeis.org/A301420>.

*Commentary.*

This polynomial is (1+X)^5-1. Its zero constant coefficient permits formal logarithm substitution.

**Definition 1.10 (Unsigned logarithmic aggregate).**

$$unsignedLog = -\frac{1}{5} \cdot \operatorname{subst}\left(-dataSeries, \operatorname{log}\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.unsignedLog` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gregory Gerard Wojnar (2018). *OEIS A301420: positive coefficients of five-data generalized Chebyshev polynomials*. URL: <https://oeis.org/A301420>.

*Commentary.*

For every positive k, k times this series coefficient is the sum of unsigned monomial weights. Multinomial expansion and the factor-count partition prove the identity in every degree.

**Definition 1.11 (Signed logarithmic aggregate).**

$$signedLog = -\frac{1}{5} \cdot \operatorname{subst}\left(\operatorname{rescale}\left(-1, dataSeries\right), \operatorname{log}\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.signedLog` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gregory Gerard Wojnar (2018). *OEIS A301420: positive coefficients of five-data generalized Chebyshev polynomials*. URL: <https://oeis.org/A301420>.

*Commentary.*

For every positive k, k times this coefficient is the sum of literal coefficients. Rescaling contributes (-1)^k and the logarithm contributes the factor-count parity.

**Definition 1.12 (The order-fourteen relation).**

$$\forall a \in (\mathbb{N})^{+}\to\mathbb{Q},\; \operatorname{recurrence}\left(a\right)\iff(\forall n \in (\mathbb{N})^{+},\; \operatorname{a}\left(n + 14\right) = 7 \cdot \operatorname{a}\left(n + 13\right) - \operatorname{a}\left(n + 12\right) - 6 \cdot \operatorname{a}\left(n + 11\right) + 2 \cdot \operatorname{a}\left(n + 10\right) - \operatorname{a}\left(n + 9\right) + 4 \cdot \operatorname{a}\left(n + 8\right) + \operatorname{a}\left(n + 7\right) + 4 \cdot \operatorname{a}\left(n + 5\right) + 2 \cdot \operatorname{a}\left(n + 4\right) - \operatorname{a}\left(n + 3\right) - 5 \cdot \operatorname{a}\left(n + 2\right) - 4 \cdot \operatorname{a}\left(n + 1\right) - \operatorname{a}\left(n\right))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.recurrence` (`✓ std3`).

*Citation.* Gregory Gerard Wojnar (2018). *OEIS A301420: positive coefficients of five-data generalized Chebyshev polynomials*. URL: <https://oeis.org/A301420>.

*Commentary.*

The displayed relation is the FORMULA-field recurrence of A301420, interpreted at every n at least one. It makes no asymptotic claim.

**Theorem 1.13 (Generating function and recurrence).**

$$positiveSeries = \frac{1 - X \cdot (1 + X)^{4}}{\left(1 - X\right) \cdot \left(2 - (1 + X)^{5}\right)}\land\operatorname{recurrence}\left(positiveCoefficient\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a301420-positive-newton-sums` (proved) by `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a301420-positive-newton-sums","declaration_gid":"D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gregory Gerard Wojnar (2018). *OEIS A301420: positive coefficients of five-data generalized Chebyshev polynomials*. URL: <https://oeis.org/A301420>.

*Commentary.*

For any rational c, twice its positive part is |c|+c. The two aggregate logarithms therefore give positiveSeries as half the sum of their derivatives. Formal differentiation yields the stated quotient. The printed recurrence polynomial is the denominator times 1-X+X^3-X^4+X^5+X^8. Multiplication leaves a polynomial of degree at most thirteen; extracting degree n+13 proves the recurrence for all positive n. A302764 also asserts the same generating-function family. The coefficient proof here is derived from the literal sum; global proof novelty is unverified.

## References

- Truth anchor: `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.Multiplicity`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.count`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.dataSeries`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.degree`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.literalCoefficient`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.multiplicities`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.positiveCoefficient`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.positiveSeries`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.recurrence`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.result`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.signedLog`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.unsignedCoefficient`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.unsignedLog`

# Hanna's A363558 Power-of-Two Formula

## Abstract

Hanna's A363558 power-of-two coefficient formula.

**Definition 1.1 (The bilateral coefficients).**

$$\forall c: \mathbb{C}, \forall m: \mathbb{N}, \operatorname{coeffA}\left(c, m\right) = \sum_{n \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} \operatorname{PowerSeries}.\operatorname{coeff}\left(m, ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\mathbb{C}\right)))^{n} \cdot (\operatorname{PowerSeries}.\operatorname{C}\left(c\right) + (\operatorname{PowerSeries}.\operatorname{X})^{n})^{2 \cdot n}\right) + \sum_{k \in \operatorname{Finset}.\operatorname{Icc}\left(1, m\right)} \operatorname{PowerSeries}.\operatorname{coeff}\left(m, ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\mathbb{C}\right)))^{2 \cdot (k)^{2} - k} \cdot ((1 + \operatorname{PowerSeries}.\operatorname{C}\left(c\right) \cdot (\operatorname{PowerSeries}.\operatorname{X})^{k})^{2 \cdot k})^{-1}\right)$$

*Formalization.* `D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo.coeffA` (`✓ std3`).

*Citation.* Paul D. Hanna (2023). *OEIS A363558, A363559, A363561 and A363569: bilateral power sums*. URL: <https://oeis.org/A363558>.

*Commentary.*

Expansion of g.f. A(x) = Sum_{n=-oo..+oo} x^n * (2 + x^n)^(2*n). The parameter c is complex, m is a natural degree, and coeff extracts a formal power-series coefficient. The nonnegative summands are polynomials. The summand indexed by the negative integer -k is expressed as X^(2*k^2-k) times the inverse of (1+C(c)*X^k)^(2*k). Both degree-m sums are finite; no analytic convergence is asserted.

**Definition 1.2 (The A363558 sequence).**

$$\forall m: \mathbb{N}, \operatorname{a}\left(m\right) = \operatorname{coeffA}\left(2, m\right)$$

*Formalization.* `D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo.a` (`✓ std3`).

*Citation.* Paul D. Hanna (2023). *OEIS A363558, A363559, A363561 and A363569: bilateral power sums*. URL: <https://oeis.org/A363558>.

*Commentary.*

Expansion of g.f. A(x) = Sum_{n=-oo..+oo} x^n * (2 + x^n)^(2*n). The parameter is 2.

**Definition 1.3 (Hanna's A363558 conjecture).**

$$claim = (\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left((2)^{n}\right) = (4)^{(2)^{n}}))$$

*Formalization.* `D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2023). *OEIS A363558, A363559, A363561 and A363569: bilateral power sums*. URL: <https://oeis.org/A363558>.

*Commentary.*

a(2^n) = 4^(2^n) for n > 0 (conjecture). Source: OEIS A363558, FORMULA field (an unpaginated entry). Indices are natural numbers; values and numeric expressions on both sides are complex. The displayed hypotheses retain the source range.

**Theorem 1.4 (Prime-index coefficients for every complex parameter).**

$$\forall c: \mathbb{C}, \forall p: \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \implies ((3 < p) \implies (\operatorname{coeffA}\left(c, p\right) = (p: \mathbb{C}) \cdot (c)^{p - 1} + (c)^{2 \cdot p}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo.coeffA_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A363558, A363559, A363561 and A363569: bilateral power sums*. URL: <https://oeis.org/A363558>.

*Commentary.*

For a prime greater than three, the divisor sums have only the two endpoint divisors. The smaller positive contribution vanishes, and the negative contribution has even exponent. This identity gives the four prime-index sequence formulas.

**Theorem 1.5 (Dyadic coefficients for every complex parameter).**

$$\forall c: \mathbb{C}, \forall N: \mathbb{N}, (0 < N) \implies (\operatorname{coeffA}\left(c, (2)^{N}\right) = (c)^{(2)^{N + 1}})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo.coeffA_pow_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A363558, A363559, A363561 and A363569: bilateral power sums*. URL: <https://oeis.org/A363558>.

*Commentary.*

For a positive dyadic exponent, pair the positive term at divisor 2^i with the negative term at divisor 2^(N-1-i). Their binomial coefficients agree and their signs are opposite. The largest positive divisor contributes the remaining power. The four dyadic sequence formulas are instances of this identity.

**Theorem 1.6 (The A363558 power-of-two formula).**

$$\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left((2)^{n}\right) = (4)^{(2)^{n}})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A363558, A363559, A363561 and A363569: bilateral power sums*. URL: <https://oeis.org/A363558>.

*Commentary.*

Apply the complex-parameter dyadic coefficient identity and simplify the indicated parameter powers.

## References

- Truth anchor: `D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo.a`
- Truth anchor: `D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo.claim`
- Truth anchor: `D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo.coeffA`
- Truth anchor: `D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo.coeffA_pow_two`
- Truth anchor: `D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo.coeffA_prime`
- Truth anchor: `D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo.result`

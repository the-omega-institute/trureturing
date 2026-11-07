# The Hermite absolute-tie generating function

## Abstract

The ordinary rational generating function of the complete increasing enumeration of physicists Hermite absolute-tie orders.

The order k and every exponent are natural numbers, including zero. The predicate HasExactlyTwo is the full-row condition from HermiteAbsoluteTieOrders: every exponent from zero through k is compared, including parity-zero coefficients. The enumeration index starts at one. All displayed series are formal power series over the rationals; no analytic convergence assertion is made.

**Definition 1.1 (The numerator polynomial).**

$$P = (((((8) \cdot (X)) + ((5) \cdot ((X)^{2}))) + ((5) \cdot ((X)^{3}))) - ((X)^{4})) - ((X)^{5})$$

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteTieGeneratingFunction.P` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mike Sheppard (2025). *Orders k of Hermite polynomials whose maximal coefficient in absolute value appears twice*. URL: <https://oeis.org/A381737/internal?rev=28>.

*Commentary.*

The numerator is exactly 8X+5X squared+5X cubed-X to the fourth-X to the fifth.

**Definition 1.2 (The denominator polynomial).**

$$D = (((1) - (X))^{3}) \cdot (((1) + (X))^{2})$$

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteTieGeneratingFunction.D` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mike Sheppard (2025). *Orders k of Hermite polynomials whose maximal coefficient in absolute value appears twice*. URL: <https://oeis.org/A381737/internal?rev=28>.

*Commentary.*

The denominator is (1-X) cubed times (1+X) squared and has constant coefficient one.

**Definition 1.3 (The complete generating-function assertion).**

$$claim = \exists a: \mathbb{N} \to \mathbb{N}, (\forall n: \mathbb{N}, (1 \le n) \implies (0 < \operatorname{a}\left(n\right))) \land ((\forall n: \mathbb{N}, \forall m: \mathbb{N}, (1 \le n) \implies ((n < m) \implies (\operatorname{a}\left(n\right) < \operatorname{a}\left(m\right)))) \land ((\forall k: \mathbb{N}, (\operatorname{HasExactlyTwo}\left(k\right)) \iff (\exists n: \mathbb{N}, ((1 \le n) \land (\operatorname{a}\left(n\right) = k)) \land (\forall m: \mathbb{N}, ((1 \le m) \land (\operatorname{a}\left(m\right) = k)) \implies (m = n)))) \land (\exists S: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{coeff}\left(0, S\right) = 0) \land ((\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, S\right) = (\operatorname{a}\left(n\right): \mathbb{Q}))) \land ((\operatorname{constantCoeff}\left(D\right) = 1) \land (S = (P) \cdot ((D)^{-1})))))))$$

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteTieGeneratingFunction.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mike Sheppard (2025). *Orders k of Hermite polynomials whose maximal coefficient in absolute value appears twice*. URL: <https://oeis.org/A381737/internal?rev=28>.

*Commentary.*

There is a positive, strictly increasing natural enumeration of every order with exactly two absolute maxima. Its zero-padded rational formal series has constant coefficient zero, coefficient a(n) at every positive index, and equals the literal numerator times the inverse of the literal denominator. The equality is in formal power series, not an analytic identity.

**Theorem 1.4 (The full A381737 Conjecture 3 generating function).**

$$\exists a: \mathbb{N} \to \mathbb{N}, (\forall n: \mathbb{N}, (1 \le n) \implies (0 < \operatorname{a}\left(n\right))) \land ((\forall n: \mathbb{N}, \forall m: \mathbb{N}, (1 \le n) \implies ((n < m) \implies (\operatorname{a}\left(n\right) < \operatorname{a}\left(m\right)))) \land ((\forall k: \mathbb{N}, (\operatorname{HasExactlyTwo}\left(k\right)) \iff (\exists n: \mathbb{N}, ((1 \le n) \land (\operatorname{a}\left(n\right) = k)) \land (\forall m: \mathbb{N}, ((1 \le m) \land (\operatorname{a}\left(m\right) = k)) \implies (m = n)))) \land (\exists S: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{coeff}\left(0, S\right) = 0) \land ((\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, S\right) = (\operatorname{a}\left(n\right): \mathbb{Q}))) \land ((\operatorname{constantCoeff}\left(D\right) = 1) \land (S = (P) \cdot ((D)^{-1})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/HermiteTieGeneratingFunction.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a381737-hermite-tie-generating-function` (proved) by `D5/S3/Analytic/Polynomial/HermiteTieGeneratingFunction.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a381737-hermite-tie-generating-function","declaration_gid":"D5/S3/Analytic/Polynomial/HermiteTieGeneratingFunction.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mike Sheppard (2025). *Orders k of Hermite polynomials whose maximal coefficient in absolute value appears twice*. URL: <https://oeis.org/A381737/internal?rev=28>.

*Commentary.*

Reuse HermiteAbsoluteTieOrders.result for the exhaustive positive enumeration. Construct the series from the three standard binomial series T0=1/(1-X), T1=1/(1-X) squared, and T2=1/(1-X) cubed, together with the rescaled series T1(-X). The combination 4T2-2T1-2T0-T1(-X)+1 has zero constant coefficient and has coefficient 2n(n+2)+(n+1)(-1)^(n+1) at every positive n. The standard binomial identities give the product with (1-X) cubed(1+X) squared equal to the numerator; constant coefficient one then permits the formal inverse. Natural-number casts are discharged from the positivity of the existing integer formula. The statement is over all k and all positive n and contains no finite prefix, selected subfamily, recurrence proxy, a0 extension, or convergence condition.

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteTieGeneratingFunction.D`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteTieGeneratingFunction.P`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteTieGeneratingFunction.claim`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteTieGeneratingFunction.result`
- Dependency: [D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders](HermiteAbsoluteTieOrders.md)

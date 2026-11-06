# Hanna's first negative coefficients exist for every parameter

## Abstract

Every integral solution of Hanna's equation for n at least two has a negative coefficient, giving infinite defined domains for the four associated sequences.

**Definition 1.1 (The integral formal-series equation).**

$$\forall n \in \mathbb{N},\; \forall F \in \operatorname{PowerSeries}\left(\mathbb{Z}\right),\; \operatorname{Shared.SeriesEquation}\left(n, F\right) \Leftrightarrow F = 1 + \operatorname{PowerSeries.X} \cdot F^{2} - \operatorname{PowerSeries.X}^{n} \cdot F^{2 \cdot n}$$

*Formalization.* `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.SeriesEquation` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A395835–A395838: first negative coefficients of an algebraic power series*. URL: <https://oeis.org/A395835>.

*Commentary.*

Define F(n,x) as the power series in x satisfying F(n,x) = 1 + x*F(n,x)^2 - x^n*F(n,x)^(2*n), then for n >= 2, a(n) = M where x^M is the first power of x with a negative coefficient in F(n,x). Should no such M exist for some n, then there are no further terms and this sequence would be finite. OEIS NAME, revision 48; no printed page number. F is an integral formal power series, x is PowerSeries.X, and 2*n is an ordinary multiplicative exponent.

**Definition 1.2 (Every required earlier parameter is defined).**

$$\forall N \in \mathbb{N},\; \operatorname{Shared.DefinedThrough}\left(N\right) \Leftrightarrow \left(\forall n \in \mathbb{N},\; 2 \le n \Rightarrow \left(n \le N \Rightarrow \left(\exists F \in \operatorname{PowerSeries}\left(\mathbb{Z}\right),\; \operatorname{Shared.SeriesEquation}\left(n, F\right) \land \left(\exists M \in \mathbb{N},\; \operatorname{IsLeast}\left(\{m: \mathbb{N} \mid \operatorname{PowerSeries.coeff}\left(m, F\right) < 0\}, M\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.DefinedThrough` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A395835–A395838: first negative coefficients of an algebraic power series*. URL: <https://oeis.org/A395835>.

*Commentary.*

The source stopping sentence is: Should no such M exist for some n, then there are no further terms and this sequence would be finite. OEIS A395835 NAME, revision 48; no printed page number. DefinedThrough N requires every natural parameter from 2 through N. IsLeast selects the first strictly negative coefficient.

**Definition 1.3 (The A395835 term relation).**

$$\forall n \in \mathbb{N},\; \forall a \in \mathbb{Z},\; \operatorname{A395835.Term835}\left(n, a\right) \Leftrightarrow \left(2 \le n \land \left(\operatorname{Shared.DefinedThrough}\left(n\right) \land \left(\exists F \in \operatorname{PowerSeries}\left(\mathbb{Z}\right),\; \exists M \in \mathbb{N},\; \operatorname{Shared.SeriesEquation}\left(n, F\right) \land \left(\operatorname{IsLeast}\left(\{m: \mathbb{N} \mid \operatorname{PowerSeries.coeff}\left(m, F\right) < 0\}, M\right) \land a = (M: \mathbb{Z})\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.Term835` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A395835–A395838: first negative coefficients of an algebraic power series*. URL: <https://oeis.org/A395835>.

*Commentary.*

Define F(n,x) as the power series in x satisfying F(n,x) = 1 + x*F(n,x)^2 - x^n*F(n,x)^(2*n), then for n >= 2, a(n) = M where x^M is the first power of x with a negative coefficient in F(n,x). Should no such M exist for some n, then there are no further terms and this sequence would be finite. OEIS NAME; no printed page number. The parameter n is natural and a is integral. DefinedThrough n enforces the stopping rule. The index M is natural and is coerced to the integers when read as a value.

**Definition 1.4 (The A395835 infinitude conjecture).**

$$\operatorname{A395835.claim} \Leftrightarrow \operatorname{Set.Infinite}\left(\{n: \mathbb{N} \mid \exists a \in \mathbb{Z},\; \operatorname{A395835.Term835}\left(n, a\right)\}\right)$$

*Formalization.* `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A395835–A395838: first negative coefficients of an algebraic power series*. URL: <https://oeis.org/A395835>.

*Commentary.*

Conjecture: this sequence is infinite. OEIS A395835 COMMENTS; no printed page number. This means an infinite domain of defined indices n, with an integral value a at each such index. It imposes no distinctness condition on the values.

**Theorem 1.5 (The A395835 domain is infinite).**

$$\operatorname{Set.Infinite}\left(\{n: \mathbb{N} \mid \exists a \in \mathbb{Z},\; \operatorname{A395835.Term835}\left(n, a\right)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A395835–A395838: first negative coefficients of an algebraic power series*. URL: <https://oeis.org/A395835>.

*Commentary.*

For every n at least two the unique integral solution has a negative coefficient. Well ordering gives its first negative index, hence every required prefix and each of the four readouts exists. These are four equivalent infinitude assertions with one shared existence proof. Assuming nonnegative coefficients forces a finite positive radius R and a bounded increasing real sum with limit L. With t=R*L^2, the numerator 1-t+(2*n-1)*t^n is positive. The rational map t/(1+t-t^n)^2 therefore has a local analytic inverse at the positive boundary, contradicting the Pringsheim obstruction. The related questions are OEIS A395835, A395836, A395837 and A395838.

**Definition 1.6 (The A395836 term relation).**

$$\forall n \in \mathbb{N},\; \forall a \in \mathbb{Z},\; \operatorname{A395836.Term836}\left(n, a\right) \Leftrightarrow \left(2 \le n \land \left(\operatorname{Shared.DefinedThrough}\left(n\right) \land \left(\exists F \in \operatorname{PowerSeries}\left(\mathbb{Z}\right),\; \exists M \in \mathbb{N},\; \operatorname{Shared.SeriesEquation}\left(n, F\right) \land \left(\operatorname{IsLeast}\left(\{m: \mathbb{N} \mid \operatorname{PowerSeries.coeff}\left(m, F\right) < 0\}, M\right) \land a = \left|\operatorname{PowerSeries.coeff}\left(M, F\right)\right|\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.Term836` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A395835–A395838: first negative coefficients of an algebraic power series*. URL: <https://oeis.org/A395835>.

*Commentary.*

Define F(n,x) as the power series in x satisfying F(n,x) = 1 + x*F(n,x)^2 - x^n*F(n,x)^(2*n), then for n >= 2, a(n) = abs( [x^M] F(n,x) ) where x^M is the first power of x with a negative coefficient in F(n,x). Should no such M exist for some n, then there are no further terms and this sequence would be finite. OEIS NAME; no printed page number. The parameter n is natural and a is integral. DefinedThrough n enforces the stopping rule. The index M is natural and is coerced to the integers when read as a value.

**Definition 1.7 (The A395836 infinitude conjecture).**

$$\operatorname{A395836.claim836} \Leftrightarrow \operatorname{Set.Infinite}\left(\{n: \mathbb{N} \mid \exists a \in \mathbb{Z},\; \operatorname{A395836.Term836}\left(n, a\right)\}\right)$$

*Formalization.* `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.claim836` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A395835–A395838: first negative coefficients of an algebraic power series*. URL: <https://oeis.org/A395835>.

*Commentary.*

Conjecture: this sequence is infinite. OEIS A395836 COMMENTS; no printed page number. This means an infinite domain of defined indices n, with an integral value a at each such index. It imposes no distinctness condition on the values.

**Theorem 1.8 (The A395836 domain is infinite).**

$$\operatorname{Set.Infinite}\left(\{n: \mathbb{N} \mid \exists a \in \mathbb{Z},\; \operatorname{A395836.Term836}\left(n, a\right)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.result836` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A395835–A395838: first negative coefficients of an algebraic power series*. URL: <https://oeis.org/A395835>.

*Commentary.*

For every n at least two the unique integral solution has a negative coefficient. Well ordering gives its first negative index, hence every required prefix and each of the four readouts exists. These are four equivalent infinitude assertions with one shared existence proof. Assuming nonnegative coefficients forces a finite positive radius R and a bounded increasing real sum with limit L. With t=R*L^2, the numerator 1-t+(2*n-1)*t^n is positive. The rational map t/(1+t-t^n)^2 therefore has a local analytic inverse at the positive boundary, contradicting the Pringsheim obstruction. The related questions are OEIS A395835, A395836, A395837 and A395838.

**Definition 1.9 (The A395837 term relation).**

$$\forall n \in \mathbb{N},\; \forall a \in \mathbb{Z},\; \operatorname{A395837.Term837}\left(n, a\right) \Leftrightarrow \left(2 \le n \land \left(\operatorname{Shared.DefinedThrough}\left(n\right) \land \left(\exists F \in \operatorname{PowerSeries}\left(\mathbb{Z}\right),\; \exists M \in \mathbb{N},\; \operatorname{Shared.SeriesEquation}\left(n, F\right) \land \left(\operatorname{IsLeast}\left(\{m: \mathbb{N} \mid \operatorname{PowerSeries.coeff}\left(m, F\right) < 0\}, M\right) \land a = \operatorname{PowerSeries.coeff}\left(M - 1, F\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.Term837` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A395835–A395838: first negative coefficients of an algebraic power series*. URL: <https://oeis.org/A395835>.

*Commentary.*

Define F(n,x) as the power series in x satisfying F(n,x) = 1 + x*F(n,x)^2 - x^n*F(n,x)^(2*n), then for n >= 2, a(n) = [x^(M-1)] F(n,x) where x^M is the first power of x with a negative coefficient in F(n,x). Should no such M exist for some n, then there are no further terms and this sequence would be finite. OEIS NAME; no printed page number. The parameter n is natural and a is integral. DefinedThrough n enforces the stopping rule. M-1 is natural predecessor subtraction. The equation forces the constant coefficient to be one, so the first negative index is positive.

**Definition 1.10 (The A395837 infinitude conjecture).**

$$\operatorname{A395837.claim837} \Leftrightarrow \operatorname{Set.Infinite}\left(\{n: \mathbb{N} \mid \exists a \in \mathbb{Z},\; \operatorname{A395837.Term837}\left(n, a\right)\}\right)$$

*Formalization.* `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.claim837` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A395835–A395838: first negative coefficients of an algebraic power series*. URL: <https://oeis.org/A395835>.

*Commentary.*

Conjecture: this sequence is infinite. OEIS A395837 COMMENTS; no printed page number. This means an infinite domain of defined indices n, with an integral value a at each such index. It imposes no distinctness condition on the values.

**Theorem 1.11 (The A395837 domain is infinite).**

$$\operatorname{Set.Infinite}\left(\{n: \mathbb{N} \mid \exists a \in \mathbb{Z},\; \operatorname{A395837.Term837}\left(n, a\right)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.result837` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A395835–A395838: first negative coefficients of an algebraic power series*. URL: <https://oeis.org/A395835>.

*Commentary.*

For every n at least two the unique integral solution has a negative coefficient. Well ordering gives its first negative index, hence every required prefix and each of the four readouts exists. These are four equivalent infinitude assertions with one shared existence proof. Assuming nonnegative coefficients forces a finite positive radius R and a bounded increasing real sum with limit L. With t=R*L^2, the numerator 1-t+(2*n-1)*t^n is positive. The rational map t/(1+t-t^n)^2 therefore has a local analytic inverse at the positive boundary, contradicting the Pringsheim obstruction. The related questions are OEIS A395835, A395836, A395837 and A395838.

**Definition 1.12 (The A395838 term relation).**

$$\forall n \in \mathbb{N},\; \forall a \in \mathbb{Z},\; \operatorname{A395838.Term838}\left(n, a\right) \Leftrightarrow \left(2 \le n \land \left(\operatorname{Shared.DefinedThrough}\left(n + 1\right) \land \left(\exists F \in \operatorname{PowerSeries}\left(\mathbb{Z}\right),\; \exists G \in \operatorname{PowerSeries}\left(\mathbb{Z}\right),\; \exists M \in \mathbb{N},\; \exists N \in \mathbb{N},\; \operatorname{Shared.SeriesEquation}\left(n, F\right) \land \left(\operatorname{IsLeast}\left(\{m: \mathbb{N} \mid \operatorname{PowerSeries.coeff}\left(m, F\right) < 0\}, M\right) \land \left(\operatorname{Shared.SeriesEquation}\left(n + 1, G\right) \land \left(\operatorname{IsLeast}\left(\{m: \mathbb{N} \mid \operatorname{PowerSeries.coeff}\left(m, G\right) < 0\}, N\right) \land a = (N: \mathbb{Z}) - (M: \mathbb{Z})\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.Term838` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A395835–A395838: first negative coefficients of an algebraic power series*. URL: <https://oeis.org/A395835>.

*Commentary.*

First differences of A395835. OEIS NAME; no printed page number. The parameter n is natural and a is integral. The forward difference is M(n+1)-M(n). The published table prepends M(2) and shifts this tail by one place; this preserves finite versus infinite length. DefinedThrough(n+1) requires both terms and every preceding term.

**Definition 1.13 (The A395838 infinitude conjecture).**

$$\operatorname{A395838.claim838} \Leftrightarrow \operatorname{Set.Infinite}\left(\{n: \mathbb{N} \mid \exists a \in \mathbb{Z},\; \operatorname{A395838.Term838}\left(n, a\right)\}\right)$$

*Formalization.* `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.claim838` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A395835–A395838: first negative coefficients of an algebraic power series*. URL: <https://oeis.org/A395835>.

*Commentary.*

Conjecture: this sequence is infinite. OEIS A395838 COMMENTS; no printed page number. This means an infinite domain of defined indices n, with an integral value a at each such index. It imposes no distinctness condition on the values.

**Theorem 1.14 (The A395838 domain is infinite).**

$$\operatorname{Set.Infinite}\left(\{n: \mathbb{N} \mid \exists a \in \mathbb{Z},\; \operatorname{A395838.Term838}\left(n, a\right)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.result838` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A395835–A395838: first negative coefficients of an algebraic power series*. URL: <https://oeis.org/A395835>.

*Commentary.*

For every n at least two the unique integral solution has a negative coefficient. Well ordering gives its first negative index, hence every required prefix and each of the four readouts exists. These are four equivalent infinitude assertions with one shared existence proof. Assuming nonnegative coefficients forces a finite positive radius R and a bounded increasing real sum with limit L. With t=R*L^2, the numerator 1-t+(2*n-1)*t^n is positive. The rational map t/(1+t-t^n)^2 therefore has a local analytic inverse at the positive boundary, contradicting the Pringsheim obstruction. The related questions are OEIS A395835, A395836, A395837 and A395838.

## References

- Truth anchor: `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.DefinedThrough`
- Truth anchor: `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.SeriesEquation`
- Truth anchor: `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.Term835`
- Truth anchor: `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.Term836`
- Truth anchor: `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.Term837`
- Truth anchor: `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.Term838`
- Truth anchor: `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.claim`
- Truth anchor: `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.claim836`
- Truth anchor: `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.claim837`
- Truth anchor: `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.claim838`
- Truth anchor: `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.result`
- Truth anchor: `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.result836`
- Truth anchor: `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.result837`
- Truth anchor: `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.result838`
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](../../../S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](../../../S1/Recurrence/Invariants/UnitReversionSquareParity.md)
- Dependency: [D5/S3/Weil/Probability/CanonicalLiNonnegativeConverse](../../Weil/Probability/CanonicalLiNonnegativeConverse.md)

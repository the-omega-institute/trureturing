# Hanna's Quadratic Exponential Has Exact Dyadic Denominators

## Abstract

Exact reduced denominators of Hanna's quadratic-exponent formal exponential.

**Definition 1.1 (The logarithmic input).**

$$logarithmInput = \operatorname{PowerSeries.mk}\left((fun m: \mathbb{N} \mapsto if m = 0 then 0 else \frac{1}{(m: \mathbb{Q}) \cdot (2: \mathbb{Q})^{m^{2}}})\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaQuadraticExponentialDyadicDenominator.logarithmInput` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A174491 and A174490: denominators of the quadratic-exponent formal exponential*. URL: <https://oeis.org/A174491>.

*Commentary.*

OEIS A174491, unpaginated %N: Denominator in the coefficient of x^n in exp( Sum_{m>=1} x^m/(m*2^(m^2)) ). The rational formal series inside the exponential has zero constant coefficient and coefficient 1/(m*2^(m^2)) at positive m.

**Definition 1.2 (The source series equation).**

$$\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSourceSeries}\left(F\right) \iff (F = \operatorname{PowerSeries.subst}\left(logarithmInput, \operatorname{PowerSeries.exp}\left(\mathbb{Q}\right)\right))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaQuadraticExponentialDyadicDenominator.IsSourceSeries` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A174491 and A174490: denominators of the quadratic-exponent formal exponential*. URL: <https://oeis.org/A174491>.

*Commentary.*

OEIS A174491, unpaginated %N: Denominator in the coefficient of x^n in exp( Sum_{m>=1} x^m/(m*2^(m^2)) ). F is a rational formal power series equal to the formal exponential of logarithmInput.

**Definition 1.3 (Hanna's denominator conjecture).**

$$claim \iff ((\exists F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSourceSeries}\left(F\right)) \land (\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSourceSeries}\left(F\right)) \implies ((\operatorname{PowerSeries.coeff}\left(0, F\right) = 1) \land ((\operatorname{Rat.den}\left(\operatorname{PowerSeries.coeff}\left(0, F\right)\right) = 1) \land (\forall n: \mathbb{N}, (1 \leq n) \implies (\operatorname{Rat.den}\left(\operatorname{PowerSeries.coeff}\left(n, F\right)\right) = 2^{n^{2} + \operatorname{padicValNat}\left(2, n\right)}))))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaQuadraticExponentialDyadicDenominator.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A174491 and A174490: denominators of the quadratic-exponent formal exponential*. URL: <https://oeis.org/A174491>.

*Commentary.*

OEIS A174491, unpaginated %F: a(n) = 2^(n^2)*A006519(n) where A006519(n) = highest power of 2 dividing n [conjecture]. Here Rat.den is the positive reduced denominator and padicValNat 2 n is the exponent of two in positive n. A006519 starts at one; the constant term and its denominator are each stated separately as one. The statement includes existence and quantifies over every rational formal series satisfying the displayed equation.

**Theorem 1.4 (Exact reduced denominator at every positive index).**

$$(\exists F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSourceSeries}\left(F\right)) \land (\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSourceSeries}\left(F\right)) \implies ((\operatorname{PowerSeries.coeff}\left(0, F\right) = 1) \land ((\operatorname{Rat.den}\left(\operatorname{PowerSeries.coeff}\left(0, F\right)\right) = 1) \land (\forall n: \mathbb{N}, (1 \leq n) \implies (\operatorname{Rat.den}\left(\operatorname{PowerSeries.coeff}\left(n, F\right)\right) = 2^{n^{2} + \operatorname{padicValNat}\left(2, n\right)})))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaQuadraticExponentialDyadicDenominator.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-a174491` (proved) by `D5/S1/Recurrence/Algebraic/HannaQuadraticExponentialDyadicDenominator.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-a174491","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaQuadraticExponentialDyadicDenominator.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A174491 and A174490: denominators of the quadratic-exponent formal exponential*. URL: <https://oeis.org/A174491>.

*Commentary.*

Differentiation gives a coefficient recurrence whose term with index zero has uniquely least two-adic valuation. For every odd prime, Fermat's identity and lifting the exponent make the logarithmic difference locally integral; the Dieudonne-Dwork criterion then excludes that prime from each reduced denominator. Prime valuations determine the denominator exactly. The same denominator assertion occurs in A174490.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaQuadraticExponentialDyadicDenominator.IsSourceSeries`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaQuadraticExponentialDyadicDenominator.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaQuadraticExponentialDyadicDenominator.logarithmInput`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaQuadraticExponentialDyadicDenominator.result`
- Dependency: [D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality](DoldExponentialIntegrality.md)

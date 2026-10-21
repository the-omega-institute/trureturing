# Hanna's A393173 Power-of-Two Parity

## Abstract

The normalized inverse-diagonal equation has integral coefficients, odd exactly at powers of two in positive degrees.

PowerSeries denotes formal power series. The operator coeff(n,A) extracts coefficient n, constantCoeff extracts the constant coefficient, C embeds a scalar as a constant series, and X is the indeterminate. The inverse is the formal power-series inverse. The displayed rational type annotations give the natural and integer coercions into the rational coefficient ring.

**Definition 1.1 (The normalized inverse-diagonal equation).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right) = ((\operatorname{constantCoeff}\left(A\right) = 1) \land (\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, (A - \operatorname{C}\left(((n: \mathbb{Q}))^{2}\right) \cdot X)^{-1}\right) = 0)))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaA393173PowerTwoParity.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A393173, squared-index inverse-diagonal parity*. URL: <https://oeis.org/A393173>.

*Commentary.*

The Name of the unpaginated OEIS A393173 entry reads: "G.f. A(x) satisfies [x^n] 1/(A(x) - n^2*x) = 0 for n >= 1." The offset-zero sequence begins with a(0)=1. Thus A has constant coefficient one, and A-C(n squared)*X has a multiplicative inverse at every natural n.

**Definition 1.2 (The parity proposition).**

$$\operatorname{claim} = ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (0 < n) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land ((\operatorname{Odd}\left(m\right)) \iff (\exists k: \mathbb{N}, n = (2)^{k}))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaA393173PowerTwoParity.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A393173, squared-index inverse-diagonal parity*. URL: <https://oeis.org/A393173>.

*Commentary.*

The Comments of the unpaginated OEIS A393173 entry state: "Conjecture: for n > 0, a(n) is odd iff n is a power of 2." Here a(n) is coeff(n,A); n and the exponent k are natural numbers. The integer m equals the rational coefficient, so the proposition asserts integrality as well as parity for every normalized rational solution. It also asserts that such a solution exists.

**Theorem 1.3 (The A393173 parity theorem).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (0 < n) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land ((\operatorname{Odd}\left(m\right)) \iff (\exists k: \mathbb{N}, n = (2)^{k})))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaA393173PowerTwoParity.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a393173-hanna-power-of-two-parity` (proved) by `D5/S1/Recurrence/Invariants/HannaA393173PowerTwoParity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a393173-hanna-power-of-two-parity","declaration_gid":"D5/S1/Recurrence/Invariants/HannaA393173PowerTwoParity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A393173, squared-index inverse-diagonal parity*. URL: <https://oeis.org/A393173>.

*Commentary.*

The degree-n coefficient of the inverse changes by the negative of the degree-n coefficient change when all earlier coefficients agree. Adding that inverse coefficient defines a strict coefficient contraction. PowerSeriesNormalizedContraction supplies its normalized fixed point over the integers and uniqueness over each commutative ring. Ring maps preserve this fixed-point equation. Over ZMod(2), the existing powerTwoSeries satisfies powerTwoSeries plus its square equals X. Hence one plus powerTwoSeries satisfies every reduced equation: at positive even n its inverse coefficient is the vanishing degree-(n+1) coefficient of powerTwoSeries; at odd n the denominator is a square and Frobenius makes its inverse coefficient vanish. Uniqueness identifies the reduction of the integral solution with this series. Rational uniqueness and the integer-cast parity equivalence prove the assertion.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA393173PowerTwoParity.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA393173PowerTwoParity.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA393173PowerTwoParity.result`
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](UnitReversionSquareParity.md)
- Dependency: [D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour](../Residue/QuotientThetaCompositionModFour.md)

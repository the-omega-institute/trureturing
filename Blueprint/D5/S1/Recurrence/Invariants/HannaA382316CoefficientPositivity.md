# Hanna's A382316 nonnegativity conjecture

## Abstract

A normalized rational solution exists, and every normalized rational solution of Hanna's equation has nonnegative coefficients.

**Definition 1.1 (The normalized source equation).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSourceSeries}\left(A\right) \iff (\operatorname{constantCoeff}\left(A\right) = 0) \land (\operatorname{coeff}\left(1, A\right) = 1) \land ((A: \operatorname{LaurentSeries}\left(\mathbb{Q}\right)) = (\operatorname{subst}\left((X^{2}: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), A\right): \operatorname{LaurentSeries}\left(\mathbb{Q}\right)) + \frac{(\operatorname{subst}\left((X^{2}: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), A\right): \operatorname{LaurentSeries}\left(\mathbb{Q}\right))^{2} \cdot (\operatorname{subst}\left((X^{3}: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), A\right): \operatorname{LaurentSeries}\left(\mathbb{Q}\right))}{(\operatorname{subst}\left((X^{6}: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), A\right): \operatorname{LaurentSeries}\left(\mathbb{Q}\right))}))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaA382316CoefficientPositivity.IsSourceSeries` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A382316, a generating-function nonnegativity conjecture*. URL: <https://oeis.org/A382316>.

*Commentary.*

OEIS A382316, NAME (unpaginated): "G.f. satisfies A(x) = A(x^2) + A(x^2)^2*A(x^3)/A(x^6), with A(0) = 0 and A'(0) = 1." FORMULA (1) (unpaginated): "(1) A(x) = A(x^2) + A(x^2)^2*A(x^3)/A(x^6)." The rational series A has constant coefficient zero and coefficient one at X. Each substitution is formed in PowerSeries Q and then coerced into LaurentSeries Q. The quotient is in that field; its denominator is nonzero because its coefficient at degree six is one.

**Definition 1.2 (The nonnegativity assertion).**

$$(\operatorname{claim} \iff (\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSourceSeries}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSourceSeries}\left(A\right) \implies \forall n: \mathbb{N}, (1 \le n) \implies (0 \le \operatorname{coeff}\left(n, A\right))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaA382316CoefficientPositivity.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A382316, a generating-function nonnegativity conjecture*. URL: <https://oeis.org/A382316>.

*Commentary.*

OEIS A382316, COMMENTS (unpaginated): "Conjecture: there are no negative terms." FORMULA (unpaginated): "G.f. A(x) = Sum_{n>=1} a(n)*x^n satisfies the following formulas." Here a(n) is coeff n A. The first OFFSET component is one; the second component is display metadata. Existence of a rational solution is asserted together with the coefficient inequalities for every normalized rational solution and every natural index at least one.

**Theorem 1.3 (Every source solution has nonnegative coefficients).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSourceSeries}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSourceSeries}\left(A\right) \implies \forall n: \mathbb{N}, (1 \le n) \implies (0 \le \operatorname{coeff}\left(n, A\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaA382316CoefficientPositivity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A382316, a generating-function nonnegativity conjecture*. URL: <https://oeis.org/A382316>.

*Commentary.*

Write A = X * f with constantCoeff f = 1. The normalized equation yields a series g with constantCoeff g = 1, f = subst (X^2) f * g and g = X + subst (X^2) f * subst (X^3) g. Strong induction proves nonnegativity of both coefficient sequences, first for g at each positive degree and then for f. A normalized coefficient contraction supplies existence. These are formal series identities and require no convergence hypothesis.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA382316CoefficientPositivity.IsSourceSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA382316CoefficientPositivity.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA382316CoefficientPositivity.result`
- Dependency: [D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity](AbsoluteReciprocalGeometricParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](UnitReversionSquareParity.md)

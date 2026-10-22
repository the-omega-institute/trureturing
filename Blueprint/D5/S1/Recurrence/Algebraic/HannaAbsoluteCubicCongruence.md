# Hanna's absolute cubic congruence for A380711

## Abstract

Coefficient contraction and reduction modulo two prove Hanna's cubic congruence.

All series have rational coefficients. The operation absSeries takes the absolute value of each coefficient. The inverse is the formal multiplicative inverse. Ring.choose is the generalized binomial coefficient over the integers; the fraction in quotient is rational division. At n = 0 it is -1.

**Definition 1.1 (Coefficientwise absolute value).**

$$\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{absSeries}\left(F\right) = \operatorname{PowerSeries}.\operatorname{mk}\left((n: \mathbb{N} \mapsto \lvert \operatorname{coeff}\left(n, F\right) \rvert)\right))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence.absSeries` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A380711: generating function and parity conjecture*. URL: <https://oeis.org/A380711>.

*Commentary.*

OEIS A380711, NAME (unpaginated): "G.f. A(x) satisfies A(x) = 1 + x*A(x)*abs( 1/A(x)^3 )." The operation abs replaces each rational coefficient by its absolute value.

**Definition 1.2 (The generating function).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right) = (A = 1 + X \cdot A \cdot \operatorname{absSeries}\left(((A)^{3})^{-1}\right)))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A380711: generating function and parity conjecture*. URL: <https://oeis.org/A380711>.

*Commentary.*

OEIS A380711, NAME (unpaginated): "G.f. A(x) satisfies A(x) = 1 + x*A(x)*abs( 1/A(x)^3 )." The offset is zero. A is a rational formal power series and X is the series variable.

**Definition 1.3 (The generalized binomial quotient).**

$$\forall n: \mathbb{N}, (\operatorname{quotient}\left(n\right) = \frac{(\operatorname{Ring}.\operatorname{choose}\left(3 \cdot (n: \mathbb{Z}) - 1, n\right): \mathbb{Q})}{3 \cdot (n: \mathbb{Q}) - 1})$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence.quotient` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A380711: generating function and parity conjecture*. URL: <https://oeis.org/A380711>.

*Commentary.*

OEIS A380711, COMMENTS (unpaginated), state "Conjecture: a(n) == binomial(3*n-1,n)/(3*n-1) (mod 2) for n >= 0." The top argument of Ring.choose is an integer. The quotient is formed in the rationals, so its value at n = 0 is binomial(-1,0)/(-1) = -1.

**Definition 1.4 (The congruence conjecture).**

$$claim = ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right))) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), ((\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (\exists m: \mathbb{Z}, (\exists z: \mathbb{Z}, ((\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land ((\operatorname{quotient}\left(n\right) = (z: \mathbb{Q})) \land (\operatorname{Int}.\operatorname{ModEq}\left(2, m, z\right))))))))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A380711: generating function and parity conjecture*. URL: <https://oeis.org/A380711>.

*Commentary.*

OEIS A380711, COMMENTS (unpaginated): "Conjecture: a(n) == binomial(3*n-1,n)/(3*n-1) (mod 2) for n >= 0." The proposition asserts existence and, for every solution and every natural index, integer representatives of both rational quantities and their congruence modulo two.

**Theorem 1.5 (The cubic congruence).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right))) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), ((\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (\exists m: \mathbb{Z}, (\exists z: \mathbb{Z}, ((\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land ((\operatorname{quotient}\left(n\right) = (z: \mathbb{Q})) \land (\operatorname{Int}.\operatorname{ModEq}\left(2, m, z\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A380711: generating function and parity conjecture*. URL: <https://oeis.org/A380711>.

*Commentary.*

Strict contraction of coefficients gives an integral solution and uniqueness over the rationals. Absolute value disappears modulo two. The reduced series satisfies F^3 = F^2 + X, so it agrees with the absolute reciprocal square-shift series. Its known binomial coefficient congruence gives the result for positive indices; at zero the two integer representatives are 1 and -1.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence.IsGF`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence.absSeries`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence.quotient`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence.result`
- Dependency: [D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity](../Invariants/AbsoluteReciprocalGeometricParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity](../Invariants/AbsoluteReciprocalSquareParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](../Invariants/PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](../Invariants/UnitReversionSquareParity.md)
- Dependency: [D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity](../Parity/AbsoluteReciprocalSquareShiftParity.md)
- Dependency: [D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime](../Residue/NegativePowerDiagonalModPrime.md)

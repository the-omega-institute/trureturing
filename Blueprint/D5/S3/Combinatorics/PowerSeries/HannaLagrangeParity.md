# Hanna's Lagrange parity conjecture for A365574

## Abstract

Triangular inversion determines Hanna's integral series and dyadic odd support.

PowerSeries has rational coefficients, X is its variable, C embeds a rational constant and coeff extracts a coefficient. The superscript -1 denotes the formal multiplicative inverse. Subtraction in natural exponents and indices is truncated natural subtraction; the restriction n > 1 makes both subtractions exact.

**Definition 1.1 (The normalized generating function).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right) = ((\operatorname{constantCoeff}\left(A\right) = 1) \land (\forall n: \mathbb{N}, ((1 < n) \implies (\operatorname{coeff}\left(n - 1, (1 + \operatorname{C}\left((n: \mathbb{Q}) + 1\right) \cdot X \cdot A)^{n} \cdot ((A)^{n})^{-1}\right) = (n: \mathbb{Q}) \cdot ((n: \mathbb{Q}) + 2)^{n - 2})))))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/HannaLagrangeParity.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2023). *OEIS A365574: generating function and parity conjecture*. URL: <https://oeis.org/A365574>.

*Commentary.*

OEIS A365574, NAME (unpaginated): "Expansion of g.f. A(x) satisfying [x^(n-1)] (1 + (n+1)*x*A(x))^n / A(x)^n = n*(n+2)^(n-2) for n > 1." The offset is zero and a(0) = 1. A is a rational formal power series; multiplication by the formal inverse expresses the displayed quotient.

**Definition 1.2 (Conjecture 1).**

$$claim = ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right))) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), ((\operatorname{IsGF}\left(A\right)) \implies (\forall k: \mathbb{N}, (\exists m: \mathbb{Z}, ((\operatorname{coeff}\left(k, A\right) = (m: \mathbb{Q})) \land ((\operatorname{Odd}\left(m\right)) \iff (\exists n: \mathbb{N}, ((1 \leq n) \land (k = (2)^{n} - 2))))))))))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/HannaLagrangeParity.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2023). *OEIS A365574: generating function and parity conjecture*. URL: <https://oeis.org/A365574>.

*Commentary.*

OEIS A365574, COMMENTS (unpaginated): "Conjecture 1: a(k) is odd iff k = 2^n - 2 for n >= 1." The proposition asserts existence of a normalized solution and integrality with the stated odd support for every normalized solution. The exponent n = 1 includes k = 0; the integer m represents the rational coefficient.

**Theorem 1.3 (The dyadic odd support).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right))) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), ((\operatorname{IsGF}\left(A\right)) \implies (\forall k: \mathbb{N}, (\exists m: \mathbb{Z}, ((\operatorname{coeff}\left(k, A\right) = (m: \mathbb{Q})) \land ((\operatorname{Odd}\left(m\right)) \iff (\exists n: \mathbb{N}, ((1 \leq n) \land (k = (2)^{n} - 2)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/HannaLagrangeParity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A365574: generating function and parity conjecture*. URL: <https://oeis.org/A365574>.

*Commentary.*

The integral series R = X(1-2X^2-2X^3)/((1-X)^2(1+2X)^2) has a compositional inverse H with linear coefficient one. Put A = H/X. Partial fractions after a Mobius substitution and Lagrange inversion give the diagonal identity. Strong induction on inverse coefficients proves uniqueness. Reduction modulo two gives H = X(1+H^2), whose coefficients are supported exactly at 2^n-1 for n >= 1.

## References

- Truth anchor: `D5/S3/Combinatorics/PowerSeries/HannaLagrangeParity.IsGF`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/HannaLagrangeParity.claim`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/HannaLagrangeParity.result`
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](../../../S1/Recurrence/Invariants/CompositionalIterateCongruence.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](../../../S1/Recurrence/Invariants/UnitReversionSquareParity.md)
- Dependency: [D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd](../../../S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo](../Nonnesting/NonnestingOneThreeTwoTwo.md)

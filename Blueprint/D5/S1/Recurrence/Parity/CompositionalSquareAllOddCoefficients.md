# All Coefficients of the A396843 Series Are Odd

## Abstract

Every positive-index coefficient in the series of OEIS A396843 is odd.

Let A be an integer formal power series with constant coefficient zero satisfying A(x A(x)-3x A(x)^2)=x^2. Reducing coefficients modulo two gives F(H)=x^2, where H=x(F+F^2).

**Theorem 1.1 (Hanna's A396843 parity conjecture).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(A\right) = 0) \implies ((\operatorname{subst}\left(A, X \cdot A - 3 \cdot X \cdot A^{2}\right) = X^{2}) \implies (\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{Odd}\left(\operatorname{coeff}\left(n, A\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/CompositionalSquareAllOddCoefficients.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396843-compositional-square-all-odd-coefficients` (proved) by `D5/S1/Recurrence/Parity/CompositionalSquareAllOddCoefficients.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396843-compositional-square-all-odd-coefficients","declaration_gid":"D5/S1/Recurrence/Parity/CompositionalSquareAllOddCoefficients.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A396843, g.f. satisfying A(x*A(x) - 3*x*A(x)^2) = x^2*. URL: <https://oeis.org/A396843>.

*Commentary.*

The coefficient of x^2 first gives coeff(1,F)=1. If two solutions agree below degree d, their inner series agree through degree d, while powers of either inner series from the second power onward cannot affect the next comparison. Hence the equation determines each coefficient successively. The series S=x/(1+x) satisfies x(S+S^2)=x^2/(1+x)^2 and therefore S(x(S+S^2))=x^2. Uniqueness gives F=S, whose every positive-degree coefficient is one modulo two.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/CompositionalSquareAllOddCoefficients.hanna_conjecture`

# Linear Exponents and the Parity of OEIS A397591

## Abstract

The integer series of OEIS A397591 exists uniquely and has odd coefficients precisely at dyadic neighbors above degree three.

The source defines A over integer formal power series with constant coefficient zero. For every m>1, [X^(m-1)](1-A)^m/(1-mX)=0. The inverse of the constant-one denominator is expressed by invOfUnit, and a(n) means the coefficient [X^n]A.

**Definition 1.1 (Construction over the integers).**

$$\operatorname{generatingSeries}\left(\right) = 1 - \operatorname{solution}\left(\right)$$

*Formalization.* `D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A397591: linear-exponent coefficient equations and dyadic neighbors*. URL: <https://oeis.org/A397591>.

*Commentary.*

Write F=1-A. At degree n>0, put e=n+1 and g=(1-eX) inverse. Let R=[X^n](F^e g) and T=[X^(n-1)](F^(e-1) F' g+F^e g squared). Differentiation gives nR=eT, so N=R-T satisfies R=eN. Changing the nth coefficient of F changes N by exactly the same amount. Successive coefficient corrections stabilize, giving an integer series F with N=0 at every positive degree. The generating series is A=1-F.

**Definition 1.2 (The exact source equation).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{DefiningEquation}\left(A\right) \iff (\operatorname{constantCoeff}\left(A\right) = 0 \land (\forall m: \mathbb{N}, 1 < m \implies \operatorname{coeff}\left(m - 1, (1 - A)^{m} \cdot \operatorname{invOfUnit}\left(1 - m \cdot X, 1\right)\right) = 0))$$

*Formalization.* `D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.DefiningEquation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A397591: linear-exponent coefficient equations and dyadic neighbors*. URL: <https://oeis.org/A397591>.

*Commentary.*

The predicate specifies integer coefficients, the zero constant term, the linear exponent m, and all natural m>1. The power-series unit inverse implements the division in the source NAME.

**Theorem 1.3 (Every defining row vanishes).**

$$\operatorname{DefiningEquation}\left(\operatorname{generatingSeries}\left(\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A397591: linear-exponent coefficient equations and dyadic neighbors*. URL: <https://oeis.org/A397591>.

*Commentary.*

Stabilization gives N=0 at each positive index. The identity R=eN and the equality of the geometric series with the denominator inverse give the original defining equation.

**Theorem 1.4 (Integer existence and uniqueness).**

$$\exists! A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{DefiningEquation}\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.integer_exists_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A397591: linear-exponent coefficient equations and dyadic neighbors*. URL: <https://oeis.org/A397591>.

*Commentary.*

The stabilized construction supplies an integer solution. If two solutions agree below degree n, their normalized residual difference equals their nth coefficient difference. Induction forces equality in every degree.

**Definition 1.5 (Coefficient indexing).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{generatingSeries}\left(\right)\right)$$

*Formalization.* `D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A397591: linear-exponent coefficient equations and dyadic neighbors*. URL: <https://oeis.org/A397591>.

*Commentary.*

The source coefficient indexing is extended by a(0)=0.

**Theorem 1.6 (Odd coefficients at dyadic neighbors).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{DefiningEquation}\left(A\right) \implies \forall n: \mathbb{N}, 3 < n \implies (\operatorname{Odd}\left(\operatorname{coeff}\left(n, A\right)\right) \iff (\exists k: \mathbb{N}, 1 < k \land (n = 2^{k} - 1 \lor n = 2^{k} + 1)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.hanna_conjecture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A397591: linear-exponent coefficient equations and dyadic neighbors*. URL: <https://oeis.org/A397591>.

*Commentary.*

Over ZMod 2, let U be the Catalan unit, so U=1+X U squared. Put E=1+X, O=EU, B=E squared+X O squared, and V=1+XU. Then B=E squared U=EO and UV=1. For each m>0, [X^m](B^m V)=0: an odd m selects an odd coefficient of a square, while an even m reduces to m/2 by the Catalan equation. This eliminates the even normalized rows of B; EO=B eliminates the odd rows. Uniqueness identifies B with the reduction of 1-A. For n>3 its coefficient is [X^n]U+[X^(n-2)]U. The frozen binary_catalan theorem says these summands are one when n+1 or n-1 is a power of two. They cannot both be one here, since two powers of two greater than two cannot differ by two. This proves the stated equivalence for every solution.

## References

- Truth anchor: `D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.DefiningEquation`
- Truth anchor: `D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.a`
- Truth anchor: `D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.generating_equation`
- Truth anchor: `D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.integer_exists_unique`
- Dependency: [D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity](../Invariants/CatalanCompositionSquareParity.md)

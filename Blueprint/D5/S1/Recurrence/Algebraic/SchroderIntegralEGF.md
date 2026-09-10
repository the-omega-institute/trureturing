# An Integral EGF And Schroeder Rows

## Abstract

The EGF coefficients in OEIS A338193 equal Kurkov's two-index recurrence.

**Remark 1.1 (Kurkov's recurrence).**

Lean statement: `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.f`

*Formalization.* `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.f` (`✓ std3`).

*Citation.* Vaclav Kotesovec; Mikhail Kurkov (2024). *OEIS A338193, an integral-defined exponential generating function and Kurkov's recurrence*. URL: <https://oeis.org/A338193>.

*Commentary.*

Set f(j,0)=1. For positive m, the boundary is f(0,m)=f(0,m-1)+m f(1,m-1). For positive j and m, use f(j,m)=f(j-1,m)+m(f(j,m-1)+f(j+1,m-1)). Recursion first decreases m, then j; all values are natural numbers.

**Remark 1.2 (The original integral equation).**

Lean statement: `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.Original`

*Formalization.* `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.Original` (`✓ std3`).

*Citation.* Vaclav Kotesovec; Mikhail Kurkov (2024). *OEIS A338193, an integral-defined exponential generating function and Kurkov's recurrence*. URL: <https://oeis.org/A338193>.

*Commentary.*

A has constant coefficient one and satisfies A=1+Integral ((x/A)' / (x/A^2)') dx. Integration is formal, with constant term zero, and all series have rational coefficients. The inverse series and the derivative in the denominator have constant coefficient one.

**Remark 1.3 (Existence and coefficient uniqueness).**

Lean statement: `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.original_exists_unique`

*Formalization.* `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.original_exists_unique` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Kotesovec; Mikhail Kurkov (2024). *OEIS A338193, an integral-defined exponential generating function and Kurkov's recurrence*. URL: <https://oeis.org/A338193>.

*Commentary.*

Write F(j) for the EGF of row j. The recurrence gives F(j+1)=F(j)+x(F(j+1)+F(j+2)). Mathlib's large Schroeder series R satisfies R=1+xR+xR^2. Induction first on degree and then on j proves F(j)=F(0)R^j. The boundary gives B'=F(0) for B=F(0)(1-xR), and B has constant term one. Clearing the units in the original equation gives (1+x)AA'-2x(A')^2-A^2=0. Its constant-one branch is exactly (1-xR)A'=A: the alternative factor has constant term minus one. Strong induction on coefficients then proves uniqueness, canceling the nonzero rational factor n+1.

**Remark 1.4 (The series specified by the source equation).**

Lean statement: `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.A`

*Formalization.* `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.A` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Kotesovec; Mikhail Kurkov (2024). *OEIS A338193, an integral-defined exponential generating function and Kurkov's recurrence*. URL: <https://oeis.org/A338193>.

*Commentary.*

Choose the unique series satisfying Original. The selection predicate contains only the original integral equation and initial value. The recurrence and the coefficient identity are proved separately.

**Remark 1.5 (The defining equation holds).**

Lean statement: `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.A_original`

*Formalization.* `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.A_original` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Kotesovec; Mikhail Kurkov (2024). *OEIS A338193, an integral-defined exponential generating function and Kurkov's recurrence*. URL: <https://oeis.org/A338193>.

*Commentary.*

The chosen A satisfies the original integral equation and A(0)=1.

**Theorem 1.6 (The coefficient identity).**

$$\forall n \in \mathbb{N}, 1 \le n \implies n! [x^{n}]A = f\left(0, n-1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.egf_coeff_eq_f` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a338193-egf-coefficients` (proved) by `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.egf_coeff_eq_f`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a338193-egf-coefficients","declaration_gid":"D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.egf_coeff_eq_f","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Kotesovec; Mikhail Kurkov (2024). *OEIS A338193, an integral-defined exponential generating function and Kurkov's recurrence*. URL: <https://oeis.org/A338193>.

*Commentary.*

For every natural n at least one, n! times coefficient n of A equals f(0,n-1), viewed in the rationals. Uniqueness identifies A with B; differentiating shifts the EGF coefficient index by one, and B'=F(0) completes the comparison. Thus the identity also proves that every positive-index EGF coefficient is a natural number.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.A`
- Truth anchor: `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.A_original`
- Truth anchor: `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.Original`
- Truth anchor: `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.egf_coeff_eq_f`
- Truth anchor: `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.f`
- Truth anchor: `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.original_exists_unique`
- Dependency: [D5/S1/Recurrence/Residue/QuarticEGFFixedPoint](../Residue/QuarticEGFFixedPoint.md)

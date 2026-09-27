# Hanna's Shift-Square Series Is Rational Modulo Eight

## Abstract

Modulo eight the series fixed by substituting the variable minus itself is the rational function with coefficients one at even and three at odd degrees, because that function satisfies the equation modulo eight and the equation has only one solution.

**Definition 1.1 (Solutions of the equation).**

$$\forall A\in \mathbb{Z}[[X]], (\operatorname{IsSolution}(A)) \Leftrightarrow (\operatorname{constantCoeff}(A)=0 \land \operatorname{coeff}(1, A)=0 \land A \circ (X-A)=X^{2}+X \cdot A)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaShiftSquareModEight.IsSolution` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A392203, G.f. A(x) satisfies A(x - A(x)) = x^2 + x*A(x)*. URL: <https://oeis.org/A392203>.

*Commentary.*

An integer power series is a solution when its constant and linear coefficients vanish and substituting the variable minus the series into it gives the square of the variable plus the variable times the series.

**Definition 1.2 (The conjecture).**

$$(claim) \Leftrightarrow ((\exists A\in \mathbb{Z}[[X]], \operatorname{IsSolution}(A)) \land (\forall A\in \mathbb{Z}[[X]], (\operatorname{IsSolution}(A)) \Rightarrow (\forall n\in \mathbb{N}, (1\leq n) \Rightarrow (\operatorname{coeff}(2n, A) \operatorname{mod} 8=1 \land \operatorname{coeff}(2n+1, A) \operatorname{mod} 8=3))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaShiftSquareModEight.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A392203, G.f. A(x) satisfies A(x - A(x)) = x^2 + x*A(x)*. URL: <https://oeis.org/A392203>.

*Commentary.*

The source observes that the coefficients at even indices from two on are one and those at odd indices from three on are three, modulo eight. The proposition also asserts that a solution exists, so that the universal part is not vacuous.

**Theorem 1.3 (The conjecture holds).**

$$(\exists A\in \mathbb{Z}[[X]], \operatorname{IsSolution}(A)) \land (\forall A\in \mathbb{Z}[[X]], (\operatorname{IsSolution}(A)) \Rightarrow (\forall n\in \mathbb{N}, (1\leq n) \Rightarrow (\operatorname{coeff}(2n, A) \operatorname{mod} 8=1 \land \operatorname{coeff}(2n+1, A) \operatorname{mod} 8=3)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaShiftSquareModEight.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-shift-square-mod-eight` (proved) by `D5/S1/Recurrence/Invariants/HannaShiftSquareModEight.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-shift-square-mod-eight","declaration_gid":"D5/S1/Recurrence/Invariants/HannaShiftSquareModEight.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A392203, G.f. A(x) satisfies A(x - A(x)) = x^2 + x*A(x)*. URL: <https://oeis.org/A392203>.

*Commentary.*

Consider the map sending a series to the square of the variable, plus the variable times the series, minus the difference between the series evaluated at the variable minus the series and the series itself; solutions are its fixed points. For two series of order at least two agreeing below some degree, their images agree one degree further: multiplying by the variable raises the order, each power of the substituted argument of exponent at least two changes by a multiple of the difference times a series without constant term, and the leading term of the difference cancels against itself after substitution. Iterating the map from zero over the integers therefore stabilises each coefficient, and the stabilised series is a solution. Over the integers modulo eight the same estimate makes the solution unique. The series with coefficients one at even and three at odd degrees from two on equals the square of the variable plus three times its cube, divided by one minus the square of the variable; clearing these denominators turns the equation for it into a polynomial identity whose two integer sides differ by a multiple of eight, and the cleared factors have constant term one, so this series is the solution modulo eight. Reducing any integer solution modulo eight therefore gives it, which is the source's observation.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaShiftSquareModEight.IsSolution`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaShiftSquareModEight.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaShiftSquareModEight.result`

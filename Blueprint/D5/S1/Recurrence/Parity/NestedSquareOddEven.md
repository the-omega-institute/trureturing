# The Nested-Square Generating Function Has Even Odd-Index Coefficients

## Abstract

A series equal to x plus a square has even coefficients at every odd index above one, because the square pairs each term of an odd coefficient with its mirror image.

**Definition 1.1 (The substitution x over one minus x).**

$$g = X \cdot \sum_{k\geq 0} X^{k}$$

*Formalization.* `D5/S1/Recurrence/Parity/NestedSquareOddEven.shift` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A392210, G.f.: x + sq(x/(1-x) + sq(x/(1-2*x) + sq(x/(1-3*x) + ...))), an infinitely nested square*. URL: <https://oeis.org/A392210>.

*Commentary.*

The substituted series is the variable times the series all of whose coefficients are one, which is the inverse of one minus the variable. Its constant coefficient is zero, so substituting it into an integer power series is well defined.

**Definition 1.2 (The functional equation).**

$$\forall A\in \mathbb{Z}[[X]], (\operatorname{IsNestedSquareGF}(A)) \Leftrightarrow (A = X+(A \circ g)^{2})$$

*Formalization.* `D5/S1/Recurrence/Parity/NestedSquareOddEven.IsNestedSquareGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A392210, G.f.: x + sq(x/(1-x) + sq(x/(1-2*x) + sq(x/(1-3*x) + ...))), an infinitely nested square*. URL: <https://oeis.org/A392210>.

*Commentary.*

An integer power series satisfies the equation when it equals the variable plus the square of the series obtained by substituting the shift into it. Iterating the equation at the shifted argument reproduces the infinitely nested square of the source entry, since substituting the variable over one minus the variable into the variable over one minus k times the variable gives the variable over one minus k plus one times the variable.

**Definition 1.3 (The conjecture).**

$$(claim) \Leftrightarrow ((\exists A\in \mathbb{Z}[[X]], \operatorname{IsNestedSquareGF}(A)) \land (\forall A\in \mathbb{Z}[[X]], (\operatorname{IsNestedSquareGF}(A)) \Rightarrow (\forall n\in \mathbb{N}, (1<n) \Rightarrow (\operatorname{Even}(\operatorname{coeff}(2n-1, A))))))$$

*Formalization.* `D5/S1/Recurrence/Parity/NestedSquareOddEven.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A392210, G.f.: x + sq(x/(1-x) + sq(x/(1-2*x) + sq(x/(1-3*x) + ...))), an infinitely nested square*. URL: <https://oeis.org/A392210>.

*Commentary.*

The source observes that the coefficients at the odd indices two n minus one are even for every n above one. The proposition also asserts that the equation has a solution, so that the universal part is not vacuous.

**Theorem 1.4 (The conjecture holds).**

$$(\exists A\in \mathbb{Z}[[X]], \operatorname{IsNestedSquareGF}(A)) \land (\forall A\in \mathbb{Z}[[X]], (\operatorname{IsNestedSquareGF}(A)) \Rightarrow (\forall n\in \mathbb{N}, (1<n) \Rightarrow (\operatorname{Even}(\operatorname{coeff}(2n-1, A)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/NestedSquareOddEven.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-nested-square-odd-coefficients` (proved) by `D5/S1/Recurrence/Parity/NestedSquareOddEven.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-nested-square-odd-coefficients","declaration_gid":"D5/S1/Recurrence/Parity/NestedSquareOddEven.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A392210, G.f.: x + sq(x/(1-x) + sq(x/(1-2*x) + sq(x/(1-3*x) + ...))), an infinitely nested square*. URL: <https://oeis.org/A392210>.

*Commentary.*

A solution is built from the source's coefficient recurrence, in which each coefficient is the self-convolution of the binomial transform of the earlier ones: the power of the shift with exponent k has coefficient the binomial coefficient of m minus one over k minus one at degree m, so substituting the shift sends a coefficient sequence to its binomial transform, and comparing coefficients gives the equation. For any solution and any index two m plus one with m at least one, the variable contributes nothing, and the coefficient of the square is the sum over the pairs of indices adding to two m plus one. Reflecting the upper half of that range onto the lower half shows the sum to be twice the sum over the lower half, since an odd total admits no pair of equal indices.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/NestedSquareOddEven.IsNestedSquareGF`
- Truth anchor: `D5/S1/Recurrence/Parity/NestedSquareOddEven.claim`
- Truth anchor: `D5/S1/Recurrence/Parity/NestedSquareOddEven.result`
- Truth anchor: `D5/S1/Recurrence/Parity/NestedSquareOddEven.shift`

# Hanna’s A377100 mod-three conjecture

## Abstract

The normalized generating equation has an integral solution, and every positive coefficient of every normalized solution is one modulo three.

**Definition 1.1 (The normalized generating equation).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \iff ((\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land ((A: \operatorname{LaurentSeries}\left(\mathbb{Q}\right)) = (\frac{(\operatorname{subst}\left((X)^{3}, A\right): \operatorname{LaurentSeries}\left(\mathbb{Q}\right))}{(\operatorname{subst}\left((X)^{2}, A\right): \operatorname{LaurentSeries}\left(\mathbb{Q}\right))}) + (((A: \operatorname{LaurentSeries}\left(\mathbb{Q}\right)))^{2}))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaCubeSquareQuotientModThree.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2024). *OEIS A377100, a generating-function coefficient conjecture*. URL: <https://oeis.org/A377100>.

*Commentary.*

OEIS A377100, Name (unpaginated): "G.f. A(x) satisfies A(x) = A(x^3)/A(x^2) + A(x)^2." The series has rational coefficients, constant coefficient zero and coefficient one at X. The quotient is taken in LaurentSeries Q.

**Definition 1.2 (Hanna’s coefficient conjecture).**

$$(\operatorname{claim}) \iff ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (1 \le n) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land (\operatorname{Int}.\operatorname{ModEq}\left(3, m, 1\right))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaCubeSquareQuotientModThree.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2024). *OEIS A377100, a generating-function coefficient conjecture*. URL: <https://oeis.org/A377100>.

*Commentary.*

OEIS A377100, Comments (unpaginated): "Conjecture: a(n) == 1 (mod 3) for n >= 1, which has been verified for the initial 2305 terms." Here a(n) is coeff n A, n starts at one, and the integer m is coerced into Q in the coefficient equality. The proposition also asserts existence.

**Theorem 1.3 (Every positive coefficient is one modulo three).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (1 \le n) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land (\operatorname{Int}.\operatorname{ModEq}\left(3, m, 1\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaCubeSquareQuotientModThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-a377100-mod-three` (proved) by `D5/S1/Recurrence/Invariants/HannaCubeSquareQuotientModThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-a377100-mod-three","declaration_gid":"D5/S1/Recurrence/Invariants/HannaCubeSquareQuotientModThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2024). *OEIS A377100, a generating-function coefficient conjecture*. URL: <https://oeis.org/A377100>.

*Commentary.*

Writing the solution as X times a normalized series gives a coefficient contraction over every commutative ring. The integral fixed point reduces to the geometric series over ZMod 3. Injectivity into Laurent series identifies the polynomial equation with the displayed quotient.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaCubeSquareQuotientModThree.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaCubeSquareQuotientModThree.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaCubeSquareQuotientModThree.result`
- Dependency: [D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity](AbsoluteReciprocalGeometricParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](PowerSeriesNormalizedContraction.md)

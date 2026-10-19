# Hanna’s A274479 mod-three conjecture

## Abstract

The normalized generating equation has an integral solution, and every positive coefficient of every normalized solution is one modulo three.

**Definition 1.1 (The normalized generating equation).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \iff ((\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land ((A)^{2} = \operatorname{subst}\left(((X)^{2}) \cdot ((((1) - ((2) \cdot (X))) - ((4) \cdot ((X)^{2})))^{-1}), A\right))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaGeometricSquareSubstitutionModThree.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2016). *OEIS A274479, a generating-function coefficient conjecture*. URL: <https://oeis.org/A274479>.

*Commentary.*

OEIS A274479, Name (unpaginated): "G.f. satisfies: A(x)^2 = A( x^2/(1 - 2*x - 4*x^2) )." The series has rational coefficients, constant coefficient zero and coefficient one at X. The denominator has constant coefficient one, so its power-series inverse exists.

**Definition 1.2 (Hanna’s coefficient conjecture).**

$$(\operatorname{claim}) \iff ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (1 \le n) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land (\operatorname{Int}.\operatorname{ModEq}\left(3, m, 1\right))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaGeometricSquareSubstitutionModThree.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2016). *OEIS A274479, a generating-function coefficient conjecture*. URL: <https://oeis.org/A274479>.

*Commentary.*

OEIS A274479, Comments (unpaginated): "a(n) = 1 (mod 3) for n>=1 (conjecture)." Here a(n) is coeff n A, n starts at one, and the integer m is coerced into Q in the coefficient equality. The proposition also asserts existence.

**Theorem 1.3 (Every positive coefficient is one modulo three).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (1 \le n) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land (\operatorname{Int}.\operatorname{ModEq}\left(3, m, 1\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaGeometricSquareSubstitutionModThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-a274479-a377100-mod-three` (proved) by `D5/S1/Recurrence/Invariants/HannaGeometricSquareSubstitutionModThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-a274479-a377100-mod-three","declaration_gid":"D5/S1/Recurrence/Invariants/HannaGeometricSquareSubstitutionModThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2016). *OEIS A274479, a generating-function coefficient conjecture*. URL: <https://oeis.org/A274479>.

*Commentary.*

Coefficientwise contraction constructs an integral compositional inverse. Frobenius in characteristic two makes each division by two exact. Reversion gives the integral solution; uniqueness and the geometric solution over ZMod 3 give every coefficient congruence.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaGeometricSquareSubstitutionModThree.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaGeometricSquareSubstitutionModThree.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaGeometricSquareSubstitutionModThree.result`
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/ScaledReversionCongruence](ScaledReversionCongruence.md)
- Dependency: [D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree](SignedCatalanCubicSubstitutionModThree.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](UnitReversionSquareParity.md)

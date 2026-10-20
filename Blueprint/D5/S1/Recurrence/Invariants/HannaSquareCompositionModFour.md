# Hanna's Square-Composition Congruence

## Abstract

An integral power-series solution has residue two modulo four exactly at shifted powers of two above degree one.

PowerSeries denotes formal power series, X is the indeterminate, coeff(n,A) is coefficient n, and constantCoeff(A) is the constant coefficient. The argument order subst(g,A) is Mathlib's PowerSeries.subst: it means A(g). The inverse is the inverse in the power-series ring. Rational coefficients are compared with integers through the displayed rational coercion. Int.ModEq(4,m,r) means that the integers m and r are congruent modulo four.

**Definition 1.1 (The normalized generating equation).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right) = ((\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (\operatorname{subst}\left((A)^{2}, A\right) = X \cdot A \cdot (1 - 2 \cdot A)^{-1})))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaSquareCompositionModFour.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2024). *OEIS A372527, square-composition generating function*. URL: <https://oeis.org/A372527>.

*Commentary.*

The Name of the unpaginated OEIS A372527 entry reads: "Expansion of g.f. A(x) satisfying A( A(x)^2 ) = x*A(x)/(1 - 2*A(x))." The series has rational coefficients, zero constant coefficient, and linear coefficient one, as specified by the entry's offset-one data. The denominator has constant coefficient one and is therefore a unit.

**Definition 1.2 (The residue proposition).**

$$\operatorname{claim} = ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies ((\forall k: \mathbb{N}, \exists m: \mathbb{Z}, (\operatorname{coeff}\left((2)^{k} + 1, A\right) = (m: \mathbb{Q})) \land (\operatorname{Int.ModEq}\left(4, m, 2\right))) \land (\forall n: \mathbb{N}, (1 < n) \implies ((\neg (\exists k: \mathbb{N}, n = (2)^{k} + 1)) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land (\operatorname{Int.ModEq}\left(4, m, 0\right))))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaSquareCompositionModFour.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2024). *OEIS A372527, square-composition generating function*. URL: <https://oeis.org/A372527>.

*Commentary.*

The Comments of the unpaginated OEIS A372527 entry state: "Conjecture: a(2^k + 1) == 2 (mod 4) for k >= 0, and a(n) == 0 (mod 4) for n > 0 when n is not of the form 2^k + 1." Here a(n) is coeff(n,A), the integers k and n used as indices are natural numbers, and the integer m equals the indicated rational coefficient. The second clause is restricted to n greater than one because the entry's first term is a(1)=1. The proposition also asserts existence of a normalized solution.

**Theorem 1.3 (The A372527 congruence theorem).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies ((\forall k: \mathbb{N}, \exists m: \mathbb{Z}, (\operatorname{coeff}\left((2)^{k} + 1, A\right) = (m: \mathbb{Q})) \land (\operatorname{Int.ModEq}\left(4, m, 2\right))) \land (\forall n: \mathbb{N}, (1 < n) \implies ((\neg (\exists k: \mathbb{N}, n = (2)^{k} + 1)) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land (\operatorname{Int.ModEq}\left(4, m, 0\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaSquareCompositionModFour.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-a372527-square-composition-mod-four` (proved) by `D5/S1/Recurrence/Invariants/HannaSquareCompositionModFour.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-a372527-square-composition-mod-four","declaration_gid":"D5/S1/Recurrence/Invariants/HannaSquareCompositionModFour.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2024). *OEIS A372527, square-composition generating function*. URL: <https://oeis.org/A372527>.

*Commentary.*

Write A=X*B. The cleared equation becomes B*(1-2*X*B)*subst(X squared*B squared,B)=1. Taking the inverse of the last two factors defines a transformation that improves agreement by one degree among series with constant coefficient one. PowerSeriesNormalizedContraction.exists_unique_fixed supplies its normalized integer fixed point and uniqueness over each commutative ring. Multiplying by X gives the integral solution of the original equation. In ZMod(4), double the coefficients of the power-of-two series over ZMod(2). The resulting series d satisfies 2*d=0, d squared=0, and subst(X squared,d)=d-2*X. Thus X*(1+d) satisfies the cleared equation. Uniqueness identifies it with the reduction of the integer solution. Its coefficient at every degree above one is two exactly at a shifted power of two, and zero elsewhere. Rational uniqueness then gives the assertion for every normalized solution.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaSquareCompositionModFour.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaSquareCompositionModFour.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaSquareCompositionModFour.result`
- Dependency: [D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity](AbsoluteReciprocalGeometricParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour](AlternatingDyadicReversionModFour.md)
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](UnitReversionSquareParity.md)

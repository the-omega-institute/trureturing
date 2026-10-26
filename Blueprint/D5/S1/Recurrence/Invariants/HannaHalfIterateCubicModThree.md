# Hanna's Half-Iterate Conjecture Modulo Three

## Abstract

The normalized half-iterate of X + 4 X cubed has integral coefficients supported modulo three on powers of three.

PowerSeries denotes formal power series. The indeterminate is X, coeff(n,A) is its degree-n coefficient, and PowerSeries.subst(A,A) is composition. Indices are natural numbers. The integer m in the formulas is cast to the rationals when compared with a rational coefficient; Int.ModEq is integer congruence.

**Definition 1.1 (The normalized odd half-iterate).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right) = ((\forall n: \mathbb{N}, \operatorname{coeff}\left(2 \cdot n, A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (\operatorname{PowerSeries}.\operatorname{subst}\left(A, A\right) = X + 4 \cdot X^{3})))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaHalfIterateCubicModThree.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2005). *OEIS A107099, compositional half-iterate of x + 4*x^3*. URL: <https://oeis.org/A107099>.

*Commentary.*

The unpaginated OEIS A107099 Name states: "G.f. satisfies A(A(x)) = x + 4*x^3, where A(x) = Sum_{n>=0} a(n)*x^(2*n+1)." The Example states: "A(x) = 1*x + 2*x^3 - 6*x^5 + 36*x^7 - 266*x^9 + 2028*x^11 - 13596*x^13 +-..." The carrier is PowerSeries over the rationals; the even coefficients vanish and the linear coefficient is one, as in the offset-zero sequence.

**Definition 1.2 (The coefficient congruence).**

$$claim = ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, \exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land ((\neg(\exists k: \mathbb{N}, n = 3^{k})) \implies (\operatorname{Int}.\operatorname{ModEq}\left(3, m, 0\right))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaHalfIterateCubicModThree.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2005). *OEIS A107099, compositional half-iterate of x + 4*x^3*. URL: <https://oeis.org/A107099>.

*Commentary.*

The unpaginated OEIS A107099 Comments state: "Coefficients [x^n] A(x) = 0 (mod 3) except at n = 3^k (conjecture)." Existence is asserted, and every IsGF series has integer coefficients. The exponent n ranges over all natural numbers. No nonvanishing assertion at powers of three is included.

**Theorem 1.3 (Uniqueness of normalized compositional square roots).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)] [\operatorname{NoZeroDivisors}\left(R\right)], ((2: R) \neq 0) \implies (\forall f: \operatorname{PowerSeries}\left(R\right), \forall g: \operatorname{PowerSeries}\left(R\right), \forall t: \operatorname{PowerSeries}\left(R\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies ((\operatorname{constantCoeff}\left(g\right) = 0) \implies ((\operatorname{coeff}\left(1, f\right) = 1) \implies ((\operatorname{coeff}\left(1, g\right) = 1) \implies ((\operatorname{PowerSeries}.\operatorname{subst}\left(f, f\right) = t) \implies ((\operatorname{PowerSeries}.\operatorname{subst}\left(g, g\right) = t) \implies (f = g)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaHalfIterateCubicModThree.half_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2005). *OEIS A107099, compositional half-iterate of x + 4*x^3*. URL: <https://oeis.org/A107099>.

*Commentary.*

Over a commutative ring with no zero divisors in which two is nonzero, two series with zero constant coefficient and linear coefficient one are equal whenever their compositional squares equal the same series.

**Theorem 1.4 (Integrality and the congruence at every degree).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, \exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land ((\neg(\exists k: \mathbb{N}, n = 3^{k})) \implies (\operatorname{Int}.\operatorname{ModEq}\left(3, m, 0\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaHalfIterateCubicModThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-a107099-half-iterate-mod-three` (proved) by `D5/S1/Recurrence/Invariants/HannaHalfIterateCubicModThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-a107099-half-iterate-mod-three","declaration_gid":"D5/S1/Recurrence/Invariants/HannaHalfIterateCubicModThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2005). *OEIS A107099, compositional half-iterate of x + 4*x^3*. URL: <https://oeis.org/A107099>.

*Commentary.*

Correct successive degrees of an integer series beginning with X. A series of the form X + 2B has compositional residual divisible by four, so each correction is even. The compatible coefficients define an integral solution. The degree-n change in the compositional square is twice the degree-n change in the series, proving uniqueness by induction. Reflection through minus X then proves oddness. Over ZMod(3), Frobenius preserves support on powers of three, and substitution preserves this support as well. Strong induction compares the solution with its truncation and forces every other coefficient to vanish. Rational uniqueness transfers these integer coefficients to every IsGF series.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaHalfIterateCubicModThree.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaHalfIterateCubicModThree.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaHalfIterateCubicModThree.half_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaHalfIterateCubicModThree.result`
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators](../Residue/CompositionalSquareDyadicDenominators.md)

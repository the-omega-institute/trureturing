# Triple-substitution congruences modulo three

## Abstract

Hanna's normalized triple-substitution series satisfies both coefficientwise congruences modulo three.

PowerSeries.subst takes the inner series first. All indices and exponents are natural numbers; each rational congruence is expressed by an integer multiplier. The two initial coefficients select the normalized solution.

**Definition 1.1 (The normalized triple-substitution equation).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \iff ((\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (\operatorname{PowerSeries}.\operatorname{subst}\left(3 \cdot X^{2}, A\right) = 2 \cdot X^{2} + A^{2} - 2 \cdot A^{3})))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A389474, A389475 and A389472: composition-series congruences*. URL: <https://oeis.org/A389474>.

*Commentary.*

OEIS A389475, NAME (unpaginated): "G.f. A(x) satisfies A(3*x^2) = 2*x^2 + A(x)^2 - 2*A(x)^3." The displayed expansion starts x+x^2, fixing the constant coefficient zero and linear coefficient one.

**Definition 1.2 (The cube congruence).**

$$(\operatorname{claim}) \iff ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, \exists m: \mathbb{Z}, \operatorname{coeff}\left(n, A^{3} - \operatorname{PowerSeries}.\operatorname{subst}\left(X^{3}, A\right)\right) = (3: \mathbb{Q}) \cdot (m: \mathbb{Q}))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A389474, A389475 and A389472: composition-series congruences*. URL: <https://oeis.org/A389474>.

*Commentary.*

OEIS A389475, FORMULA (4.a), unpaginated: "(4.a) A(x)^3 == A(x^3) (mod 3) (conjecture)." Equality modulo three means the difference at every natural coefficient index is three times an integer; existence is included.

**Definition 1.3 (The square congruence).**

$$(\operatorname{FormulaFourB}.\operatorname{claimFourB}) \iff ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, \exists m: \mathbb{Z}, \operatorname{coeff}\left(n, A^{2} - \left(X^{2} + 2 \cdot \operatorname{PowerSeries}.\operatorname{subst}\left(X^{3}, A\right)\right)\right) = (3: \mathbb{Q}) \cdot (m: \mathbb{Q}))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.claimFourB` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A389474, A389475 and A389472: composition-series congruences*. URL: <https://oeis.org/A389474>.

*Commentary.*

OEIS A389475, FORMULA (4.b), unpaginated: "(4.b) A(x)^2 == x^2 + 2*A(x^3) (mod 3) (conjecture)." The coefficientwise rational equality has an integer multiplier and includes existence of the normalized series.

**Theorem 1.4 (The integral power congruence).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall n: \mathbb{N}, \forall k: \mathbb{N}, (3: \mathbb{Z}) \mid \operatorname{coeff}\left(n, f^{3 \cdot k} - \operatorname{PowerSeries}.\operatorname{subst}\left(X^{3}, f\right)^{k}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.integral_frobenius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A389474, A389475 and A389472: composition-series congruences*. URL: <https://oeis.org/A389474>.

*Commentary.*

For every integral power series and all natural n and k, the displayed coefficient is divisible by three. Map to ZMod 3 and apply the power-series Frobenius identity, then lift coefficient equality back to integer divisibility.

**Theorem 1.5 (The cube congruence holds).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, \exists m: \mathbb{Z}, \operatorname{coeff}\left(n, A^{3} - \operatorname{PowerSeries}.\operatorname{subst}\left(X^{3}, A\right)\right) = (3: \mathbb{Q}) \cdot (m: \mathbb{Q})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/h3894-triple-square-frobenius-mod-three` (proved) by `D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"h3894-triple-square-frobenius-mod-three","declaration_gid":"D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A389474, A389475 and A389472: composition-series congruences*. URL: <https://oeis.org/A389474>.

*Commentary.*

A389475 (4.a), #21672. Reduction modulo two makes the triangular residual coefficients even, giving an integral normalized solution. Its coefficient diagonal is minus two, so strong induction identifies all normalized rational solutions. The integral Frobenius congruence then proves the cube congruence.

**Theorem 1.6 (The square congruence holds).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, \exists m: \mathbb{Z}, \operatorname{coeff}\left(n, A^{2} - \left(X^{2} + 2 \cdot \operatorname{PowerSeries}.\operatorname{subst}\left(X^{3}, A\right)\right)\right) = (3: \mathbb{Q}) \cdot (m: \mathbb{Q})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.resultFourB` (`✓ std3`). ∎

*Resolves.* `Problems/h3894-triple-square-frobenius-mod-three` (proved) by `D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.resultFourB`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"h3894-triple-square-frobenius-mod-three","declaration_gid":"D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.resultFourB","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A389474, A389475 and A389472: composition-series congruences*. URL: <https://oeis.org/A389474>.

*Commentary.*

A389475 (4.b), #21673. The integral solution's equation reduces in characteristic three to A^2=X^2+2A^3. Frobenius replaces A^3 by A(X^3), giving the square congruence at every coefficient.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.claimFourB`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.integral_frobenius`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.result`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.resultFourB`
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](CompositionalIterateCongruence.md)
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality](HannaPrimeSubstitutionIntegrality.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](UnitReversionSquareParity.md)

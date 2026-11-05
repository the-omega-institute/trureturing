# Square coefficients modulo nine

## Abstract

The normalized solution of Hanna's composition equation has square coefficients divisible by nine beyond degree three.

The rings are formal power-series rings over the displayed coefficient rings. PowerSeries.subst takes the inner series first. The rational series has constant coefficient zero and linear coefficient one. Each rational congruence asserts an integer multiple of its modulus, so it includes the integrality needed for that congruence.

**Definition 1.1 (The normalized composition equation).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \iff ((\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (\operatorname{PowerSeries}.\operatorname{subst}\left(X^{2} + 2 \cdot X^{3} + 2 \cdot A^{2}, A\right) = 3 \cdot A^{2})))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A389474, A389475 and A389472: composition-series congruences*. URL: <https://oeis.org/A389474>.

*Commentary.*

OEIS A389474, NAME (unpaginated): "G.f. A(x) satisfies A( x^2 + 2*x^3 + 2*A(x)^2 ) = 3*A(x)^2." The displayed expansion begins x+x^2 and fixes the two normalization coefficients.

**Definition 1.2 (The square-coefficient conjecture).**

$$(\operatorname{claim}) \iff ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (3 < n) \implies (\exists m: \mathbb{Z}, \operatorname{coeff}\left(n, A^{2}\right) = (9: \mathbb{Q}) \cdot (m: \mathbb{Q})))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A389474, A389475 and A389472: composition-series congruences*. URL: <https://oeis.org/A389474>.

*Commentary.*

OEIS A389474, FORMULA (3), unpaginated: "(3) [x^n] A(x)^2 == 0 (mod 9) for n > 3 (conjecture)." The index n is natural and the multiplier m is integral; existence of a normalized rational solution is included.

**Definition 1.3 (The power-congruence conjecture).**

$$(\operatorname{FormulaFour}.\operatorname{claimFour}) \iff ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, \forall k: \mathbb{N}, (1 \le n) \implies ((1 \le k) \implies (\exists m: \mathbb{Z}, \operatorname{coeff}\left(n, A^{3 \cdot k} - \operatorname{PowerSeries}.\operatorname{subst}\left(X^{3}, A\right)^{k}\right) = (3: \mathbb{Q}) \cdot (m: \mathbb{Q}))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine.claimFour` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A389474, A389475 and A389472: composition-series congruences*. URL: <https://oeis.org/A389474>.

*Commentary.*

OEIS A389474, FORMULA (4), unpaginated: "(4) [x^n] A(x)^(3*k) - A(x^3)^k == 0 (mod 3) for n >= 1 and k >= 1 (conjecture)." Both indices are natural numbers with the stated lower bounds, and the congruence has an integer multiplier.

**Theorem 1.4 (The square-coefficient conjecture holds).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (3 < n) \implies (\exists m: \mathbb{Z}, \operatorname{coeff}\left(n, A^{2}\right) = (9: \mathbb{Q}) \cdot (m: \mathbb{Q}))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A389474, A389475 and A389472: composition-series congruences*. URL: <https://oeis.org/A389474>.

*Commentary.*

Triangular lifting gives an integral solution and coefficient induction identifies every normalized rational solution with it. Write A=X+X^2Q and H=X^2+2X^3+2A^2. The equation gives H(1+HQ(H))=3A^2. The factor with constant coefficient one has an integral inverse, so H is three times an integral series. Then A^2-X^2-2X^3=H^2Q(H) is nine times an integral series.

**Theorem 1.5 (The power-congruence conjecture holds).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, \forall k: \mathbb{N}, (1 \le n) \implies ((1 \le k) \implies (\exists m: \mathbb{Z}, \operatorname{coeff}\left(n, A^{3 \cdot k} - \operatorname{PowerSeries}.\operatorname{subst}\left(X^{3}, A\right)^{k}\right) = (3: \mathbb{Q}) \cdot (m: \mathbb{Q})))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine.resultFour` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A389474, A389475 and A389472: composition-series congruences*. URL: <https://oeis.org/A389474>.

*Commentary.*

The integral solution satisfies the coefficientwise Frobenius congruence for every exponent 3k. Identification with each normalized rational solution gives the stated integer multiples.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine.claimFour`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine.result`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine.resultFour`
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](CompositionalIterateCongruence.md)
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality](HannaPrimeSubstitutionIntegrality.md)
- Dependency: [D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree](HannaTripleSquareFrobeniusModThree.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](PowerSeriesNormalizedContraction.md)

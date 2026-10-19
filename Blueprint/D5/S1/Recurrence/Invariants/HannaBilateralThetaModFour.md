# Hanna Bilateral Theta Congruence Modulo Four

## Abstract

Hanna's A380060 equation has an integral solution with residue two exactly at positive squares.

Paul D. Hanna, OEIS A380060, Name: "G.f. A(x) satisfies A(x) = Sum_{n=-oo..+oo} x^(n^2) * (A(x) - x^n)^n/(1 - x^n*A(x))^n." Comments: "The term x^(n^2) * (A - x^n)^n/(1 - x^n*A)^n is invariant under sign reversal of n." Formula (2): "A(x) = 1 + 2*Sum_{n>=1} x^(n^2) * (A(x) - x^n)^n/(1 - x^n*A(x))^n." These are the Name, Comments and Formula sections of the unpaginated entry.

PowerSeries(Q) denotes rational formal power series. The term of index zero is one, and the terms at opposite indices coincide. IsGF uses formula (2), with the coefficient at degree m evaluated from the finite interval 1 through m. A summand of index n contains X^(n^2), so larger indices contribute zero. The inverse is the formal power-series inverse; each denominator has constant coefficient one. All exponents and coefficient indices are natural numbers. The expression (z : Q) is the integer-to-rational coercion, and the congruence and divisibility in the conclusion are over the integers.

**Definition 1.1 (The generating equation).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right) = \left(A = \operatorname{mk}\left(m: \mathbb{N} \mapsto \operatorname{coeff}\left(m, 1 + 2 \cdot \sum_{n \in \operatorname{Finset}.\operatorname{Icc}\left(1, m\right)} ((X)^{(n)^{2}} \cdot (A - (X)^{n})^{n} \cdot ((1 - (X)^{n} \cdot A)^{n})^{-1})\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaBilateralThetaModFour.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A380060, bilateral unit-quotient square series*. URL: <https://oeis.org/A380060>.

*Commentary.*

Formula (2): "A(x) = 1 + 2*Sum_{n>=1} x^(n^2) * (A(x) - x^n)^n/(1 - x^n*A(x))^n." The unpaginated OEIS Formula section is expressed coefficientwise over Q.

**Definition 1.2 (The square residue conjecture).**

$$\operatorname{claim} = ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (0 < n) \implies (\exists z: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (z: \mathbb{Q})) \land (((z \equiv 2 \pmod{4}) \iff \operatorname{IsSquare}\left(n\right)) \land ((\neg \operatorname{IsSquare}\left(n\right)) \implies ((4: \mathbb{Z}) \mid z)))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaBilateralThetaModFour.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A380060, bilateral unit-quotient square series*. URL: <https://oeis.org/A380060>.

*Commentary.*

Comments: "Conjecture: for n > 0, a(n) == 2 (mod 4) iff n is a square, and a(n) is divisible by 4 when n is nonsquare." The unpaginated OEIS comment concerns the coefficients of the series in formula (2). Here existence is included, and the residue assertion is stated for every rational solution. The integer z equals its coefficient at each positive natural index n.

**Theorem 1.3 (Hanna's A380060 conjecture).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (0 < n) \implies (\exists z: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (z: \mathbb{Q})) \land (((z \equiv 2 \pmod{4}) \iff \operatorname{IsSquare}\left(n\right)) \land ((\neg \operatorname{IsSquare}\left(n\right)) \implies ((4: \mathbb{Z}) \mid z))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaBilateralThetaModFour.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-a380060-bilateral-theta-mod-four` (proved) by `D5/S1/Recurrence/Invariants/HannaBilateralThetaModFour.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-a380060-bilateral-theta-mod-four","declaration_gid":"D5/S1/Recurrence/Invariants/HannaBilateralThetaModFour.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A380060, bilateral unit-quotient square series*. URL: <https://oeis.org/A380060>.

*Commentary.*

The integral coefficient iteration improves agreement by one degree. Its stabilized coefficients give an integer fixed point, and the same contraction identifies every rational solution with its image in Q. Modulo two the solution is one, so each unit quotient is one and its summand reduces to X^(m^2). Thus half of each positive coefficient has the parity of the positive-square theta series. Doubling gives residue two modulo four exactly at squares and divisibility by four at the other positive indices.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaBilateralThetaModFour.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaBilateralThetaModFour.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaBilateralThetaModFour.result`
- Dependency: [D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour](../Bilateral/BilateralQuarterShiftThetaModFour.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](UnitReversionSquareParity.md)
- Dependency: [D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour](../Residue/QuotientThetaCompositionModFour.md)

# Hanna's Square-Exponent Factorial Integrality

## Abstract

Existence, uniqueness and integer coefficients for Hanna's three square-exponent factorial series.

**Definition 1.1 (The finite square-power sum).**

$$\forall M: \mathbb{N}, \forall B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{squarePowerSum}\left(M, B\right) = \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(M + 1\right), (fun m: \mathbb{N} \mapsto \operatorname{HSMul.hSMul}\left(\frac{1}{(\operatorname{Nat.factorial}\left(m\right): \mathbb{Q})}, B^{m \cdot m}\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.squarePowerSum` (`✓ std3`).

*Citation.* Paul D. Hanna (2021). *OEIS A350410, A350411 and A350412: square-exponent factorial integrality*. URL: <https://oeis.org/A350410>.

*Commentary.*

The sum runs from zero through M, inclusive. Scalar division is rational and each factorial is positive.

**Definition 1.2 (The first two coefficients).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{normalized}\left(B\right)) \iff ((\operatorname{PowerSeries.constantCoeff}\left(B\right) = -1) \land (\operatorname{PowerSeries.coeff}\left(1, B\right) = 1))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.normalized` (`✓ std3`).

*Citation.* Paul D. Hanna (2021). *OEIS A350410, A350411 and A350412: square-exponent factorial integrality*. URL: <https://oeis.org/A350410>.

*Commentary.*

The first two source examples start with -1+x; the coefficients are ordinary formal power-series coefficients.

**Definition 1.3 (The degree-dependent equations).**

$$\forall cutoff: \mathbb{N} \to \mathbb{N}, \forall B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{vanishingEquation}\left(cutoff, B\right)) \iff ((\operatorname{normalized}\left(B\right)) \land (\forall n: \mathbb{N}, (2 \le n) \implies (\operatorname{PowerSeries.coeff}\left(n, \operatorname{squarePowerSum}\left(cutoff\left(n\right), B\right)\right) = 0)))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.vanishingEquation` (`✓ std3`).

*Citation.* Paul D. Hanna (2021). *OEIS A350410, A350411 and A350412: square-exponent factorial integrality*. URL: <https://oeis.org/A350410>.

*Commentary.*

The normalized rational series satisfies the coefficient equation in every degree at least two, with the upper endpoint chosen by cutoff.

**Definition 1.4 (The first source series).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350410}\left(A\right)) \iff (\operatorname{vanishingEquation}\left((fun n: \mathbb{N} \mapsto n), A\right))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.isSourceA350410` (`✓ std3`).

*Citation.* Paul D. Hanna (2021). *OEIS A350410, A350411 and A350412: square-exponent factorial integrality*. URL: <https://oeis.org/A350410>.

*Commentary.*

OEIS A350410, NAME (revision 5, no page number): "G.f. A(x) = Sum_{n>=0} a(n)*x^n satisfies: 0 = [x^n] Sum_{m=0..n} A(x)^(m^2) / m!, for n > 1." The EXAMPLE starts -1+x, fixing the two initial coefficients.

**Definition 1.5 (The second source series).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350411}\left(A\right)) \iff (\operatorname{vanishingEquation}\left((fun n: \mathbb{N} \mapsto n + 1), A\right))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.isSourceA350411` (`✓ std3`).

*Citation.* Paul D. Hanna (2021). *OEIS A350410, A350411 and A350412: square-exponent factorial integrality*. URL: <https://oeis.org/A350410>.

*Commentary.*

OEIS A350411, NAME (revision 5, no page number): "G.f. A(x) = Sum_{n>=0} a(n)*x^n satisfies: 0 = [x^n] Sum_{m=0..n+1} A(x)^(m^2) / m!, for n > 1." The EXAMPLE starts -1+x, fixing the two initial coefficients.

**Definition 1.6 (The third source series).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350412}\left(A\right)) \iff ((\operatorname{PowerSeries.constantCoeff}\left(A\right) = 0) \land ((\operatorname{PowerSeries.coeff}\left(1, A\right) = 1) \land (\forall n: \mathbb{N}, (2 \le n) \implies (\operatorname{PowerSeries.coeff}\left(n, \operatorname{squarePowerSum}\left(2 \cdot n, A - 1\right)\right) = 0))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.isSourceA350412` (`✓ std3`).

*Citation.* Paul D. Hanna (2021). *OEIS A350410, A350411 and A350412: square-exponent factorial integrality*. URL: <https://oeis.org/A350410>.

*Commentary.*

OEIS A350412, NAME (revision 9, no page number): "G.f. A(x) = Sum_{n>=1} a(n)*x^n satisfies: 0 = [x^n] Sum_{m=0..2*n} (A(x) - 1)^(m^2) / m!, for n > 1, with A(0) = 0." The EXAMPLE starts x, so the degree-one coefficient is one.

**Definition 1.7 (The three integrality assertions).**

$$(\operatorname{claim}) \iff ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350410}\left(A\right)) \land (\forall Ap: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350410}\left(Ap\right)) \implies (Ap = A))) \land ((\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350410}\left(A\right)) \implies (\forall n: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(n, A\right) = (z: \mathbb{Q}))) \land ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350411}\left(A\right)) \land (\forall Ap: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350411}\left(Ap\right)) \implies (Ap = A))) \land ((\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350411}\left(A\right)) \implies (\forall n: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(n, A\right) = (z: \mathbb{Q}))) \land ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350412}\left(A\right)) \land (\forall Ap: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350412}\left(Ap\right)) \implies (Ap = A))) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350412}\left(A\right)) \implies (\forall n: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(n, A\right) = (z: \mathbb{Q}))))))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2021). *OEIS A350410, A350411 and A350412: square-exponent factorial integrality*. URL: <https://oeis.org/A350410>.

*Commentary.*

OEIS A350410, A350411 and A350412, COMMENTS (web entries, no page numbers): "This sequence is conjectured to consist entirely of integers." For each of the three preceding source equations, there is exactly one rational series with the stated initial coefficients, and every coefficient of every such series is an integer. All degrees, including zero, occur in the integer-coefficient assertions.

**Theorem 1.8 (All three series exist uniquely and have integer coefficients).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350410}\left(A\right)) \land (\forall Ap: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350410}\left(Ap\right)) \implies (Ap = A))) \land ((\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350410}\left(A\right)) \implies (\forall n: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(n, A\right) = (z: \mathbb{Q}))) \land ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350411}\left(A\right)) \land (\forall Ap: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350411}\left(Ap\right)) \implies (Ap = A))) \land ((\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350411}\left(A\right)) \implies (\forall n: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(n, A\right) = (z: \mathbb{Q}))) \land ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350412}\left(A\right)) \land (\forall Ap: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350412}\left(Ap\right)) \implies (Ap = A))) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{isSourceA350412}\left(A\right)) \implies (\forall n: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(n, A\right) = (z: \mathbb{Q})))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-hanna350410` (proved) by `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-hanna350410","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2021). *OEIS A350410, A350411 and A350412: square-exponent factorial integrality*. URL: <https://oeis.org/A350410>.

*Commentary.*

The factorial slope is nonzero. Differentiation makes the exceptional last numerator divisible by the cutoff; the remaining factorials already divide the clearing factorial. The resulting integer coefficient operator has a fixed point by prefix contraction. Translation by one gives the third series.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.isSourceA350410`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.isSourceA350411`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.isSourceA350412`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.normalized`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.result`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.squarePowerSum`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality.vanishingEquation`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaA181070Integrality](HannaA181070Integrality.md)
- Dependency: [D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure](HannaLogarithmicPowerClosure.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](../Invariants/PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](../Invariants/UnitReversionSquareParity.md)
- Dependency: [D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport](../LinearRows/LinearExponentDyadicSupport.md)

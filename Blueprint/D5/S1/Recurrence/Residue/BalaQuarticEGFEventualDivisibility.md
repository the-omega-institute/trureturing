# Bala's A281428 Eventual Divisibility Conjecture

## Abstract

Every positive modulus coprime to six eventually divides the A281428 coefficients.

All series are rational formal power series. The integral has constant coefficient zero. The exponentials below are substitutions into PowerSeries.exp. For the sequence in the OEIS example, a(n)=(2n)! times coeff(2n,C); odd degrees are omitted. All indices and moduli are natural numbers. Equality to N times an integer expresses integer divisibility.

**Definition 1.1 (The source equation).**

$$\forall C: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSourceSeries}\left(C\right) \iff ((\operatorname{PowerSeries.constantCoeff}\left(C\right) = 1) \land (C = \operatorname{PowerSeries.C}\left(\frac{1}{2}\right) \cdot (\operatorname{PowerSeries.subst}\left(\operatorname{PowerSeries.mk}\left((fun j: \mathbb{N} \mapsto match j with \mid 0 \mapsto 0 \mid k + 1 \mapsto \frac{\operatorname{PowerSeries.coeff}\left(k, C^{4}\right)}{(k + 1: \mathbb{Q})})\right), \operatorname{PowerSeries.exp}\left(\mathbb{Q}\right)\right) + \operatorname{PowerSeries.subst}\left(-\operatorname{PowerSeries.mk}\left((fun j: \mathbb{N} \mapsto match j with \mid 0 \mapsto 0 \mid k + 1 \mapsto \frac{\operatorname{PowerSeries.coeff}\left(k, C^{4}\right)}{(k + 1: \mathbb{Q})})\right), \operatorname{PowerSeries.exp}\left(\mathbb{Q}\right)\right))))$$

*Formalization.* `D5/S1/Recurrence/Residue/BalaQuarticEGFEventualDivisibility.IsSourceSeries` (`✓ std3`).

*Citation.* Paul D. Hanna; Peter Bala (2026). *OEIS A281428: quartic hyperbolic exponential generating function, conjecture 1*. URL: <https://oeis.org/A281428>.

*Commentary.*

OEIS A281428, revision 49, NAME (no page number): "E.g.f. C(x) satisfies C(x) = cosh( Integral C(x)^4 dx )." The EXAMPLE starts with 1 + x^2/2! + 17*x^4/4!, so C has constant coefficient one. The displayed equation writes cosh as the half-sum of two exponential substitutions.

**Definition 1.2 (Bala's first conjecture).**

$$claim \iff ((\exists C: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSourceSeries}\left(C\right)) \land (\forall C: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSourceSeries}\left(C\right)) \implies (\forall N: \mathbb{N}, (0 < N) \implies ((\operatorname{Nat.Coprime}\left(N, 6\right)) \implies (\exists n0: \mathbb{N}, \forall n: \mathbb{N}, (n0 \le n) \implies (\exists k: \mathbb{Z}, (\operatorname{Nat.factorial}\left(2 \cdot n\right): \mathbb{Q}) \cdot \operatorname{PowerSeries.coeff}\left(2 \cdot n, C\right) = (N: \mathbb{Q}) \cdot (k: \mathbb{Q})))))))$$

*Formalization.* `D5/S1/Recurrence/Residue/BalaQuarticEGFEventualDivisibility.claim` (`✓ std3`).

*Citation.* Paul D. Hanna; Peter Bala (2026). *OEIS A281428: quartic hyperbolic exponential generating function, conjecture 1*. URL: <https://oeis.org/A281428>.

*Commentary.*

OEIS A281428, revision 49, COMMENTS, Peter Bala, item 1 (no page number): "1) If N is not divisble by either 2 or 3 then there exists n_0 such that N divides a(n) for all n >= n_0." The EXAMPLE uses even-degree factorial normalization. The existence conjunct asserts that the original normalized series equation has a solution.

**Theorem 1.3 (Eventual divisibility for every coprime modulus).**

$$(\exists C: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSourceSeries}\left(C\right)) \land (\forall C: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSourceSeries}\left(C\right)) \implies (\forall N: \mathbb{N}, (0 < N) \implies ((\operatorname{Nat.Coprime}\left(N, 6\right)) \implies (\exists n0: \mathbb{N}, \forall n: \mathbb{N}, (n0 \le n) \implies (\exists k: \mathbb{Z}, (\operatorname{Nat.factorial}\left(2 \cdot n\right): \mathbb{Q}) \cdot \operatorname{PowerSeries.coeff}\left(2 \cdot n, C\right) = (N: \mathbb{Q}) \cdot (k: \mathbb{Q}))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/BalaQuarticEGFEventualDivisibility.result` (`✓ std3`). ∎

*Resolves.* `Problems/bala281428` (proved) by `D5/S1/Recurrence/Residue/BalaQuarticEGFEventualDivisibility.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bala281428","declaration_gid":"D5/S1/Recurrence/Residue/BalaQuarticEGFEventualDivisibility.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna; Peter Bala (2026). *OEIS A281428: quartic hyperbolic exponential generating function, conjecture 1*. URL: <https://oeis.org/A281428>.

*Commentary.*

The differential system gives integer factorial-normalized coefficients. With S the corresponding hyperbolic sine and u=S/C, one obtains u-u^3/3=X and (1-u^2)C^2=1. Degree induction places the ordinary coefficients in every rational subring containing 1/2 and 1/3. Their reduced denominators are therefore coprime to N. For n at least (N+1)/2, with natural division, N divides (2n)!, and integer Euclid cancellation proves the assertion. This sufficient onset is not asserted minimal.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/BalaQuarticEGFEventualDivisibility.IsSourceSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/BalaQuarticEGFEventualDivisibility.claim`
- Truth anchor: `D5/S1/Recurrence/Residue/BalaQuarticEGFEventualDivisibility.result`
- Dependency: [D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality](../Algebraic/DoldExponentialIntegrality.md)
- Dependency: [D5/S1/Recurrence/Algebraic/SchroderIntegralEGF](../Algebraic/SchroderIntegralEGF.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](../Invariants/PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](../Invariants/UnitReversionSquareParity.md)
- Dependency: [D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd](DiagonalPowerRatioAllOdd.md)
- Dependency: [D5/S1/Recurrence/Residue/IntegralEGFComposition](IntegralEGFComposition.md)
- Dependency: [D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence](ParametricExponentialSquareCongruence.md)

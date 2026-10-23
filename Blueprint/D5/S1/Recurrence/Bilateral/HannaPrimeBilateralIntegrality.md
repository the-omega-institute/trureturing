# Hanna's Prime Bilateral Integrality Conjecture

## Abstract

The normalized bilateral equation has an integral solution exactly at prime parameters.

PowerSeries and LaurentSeries are formal series over the rationals. The parameter p and coefficient indices N, K, n are natural numbers; j is an integer. HahnSeries.ofPowerSeries embeds power series in Laurent series, where powers have integer exponents. Natural numbers and integers in rational expressions are cast to the rationals. The parameter range is p at least two.

**Definition 1.1 (The Laurent-series summand).**

$$\forall p: \mathbb{N}, \forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \forall n: \mathbb{Z}, \operatorname{term}\left(p, F, n\right) = (\operatorname{let} x: \operatorname{LaurentSeries}\left(\mathbb{Q}\right) = \operatorname{HahnSeries}.\operatorname{ofPowerSeries}\left(\mathbb{Z}, \mathbb{Q}, X\right); \operatorname{let} G: \operatorname{LaurentSeries}\left(\mathbb{Q}\right) = \operatorname{HahnSeries}.\operatorname{ofPowerSeries}\left(\mathbb{Z}, \mathbb{Q}, F\right); ((-(1): \operatorname{LaurentSeries}\left(\mathbb{Q}\right)))^{n} \cdot (x)^{(p: \mathbb{Z}) \cdot n} \cdot ((G + (x)^{n}))^{(p: \mathbb{Z}) \cdot n})$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaPrimeBilateralIntegrality.term` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A380681–A380686, prime parameters and integral bilateral series*. URL: <https://oeis.org/A380681>.

*Commentary.*

The unpaginated Comments of OEIS A380681 state: "Conjecture: if F(x) satisfies p*x = Sum_{n=-oo..+oo} (-1)^n * x^(p*n) * (F(x) + x^n)^(p*n) with F(0) = 1 for some fixed integer p, then F(x) is an integer series in x iff p is prime. The g.f. A(x) of this sequence is the case when p = 2; other cases include A380682 (p=3), A380683 (p=5), A380684 (p=7), A380685 (p=11), and A380686 (p=13)." Here x is the embedded indeterminate and G is the embedded F. The sign and the two remaining factors use the source's integer exponents.

**Definition 1.2 (The coefficientwise bilateral equation).**

$$\forall p: \mathbb{N}, \forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSolution}\left(p, F\right) = ((\operatorname{constantCoeff}\left(F\right) = 1) \land (\forall N: \mathbb{N}, \forall K: \mathbb{N}, (N + 1 \le K) \implies (\sum_{j \in \operatorname{Finset}.\operatorname{Icc}\left(-((K: \mathbb{Z})), (K: \mathbb{Z})\right)} (\operatorname{HahnSeries}.\operatorname{coeff}\left(\operatorname{term}\left(p, F, j\right), (N: \mathbb{Z})\right)) = \operatorname{if} (N = 1) \operatorname{then} (p: \mathbb{Q}) \operatorname{else} 0)))$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaPrimeBilateralIntegrality.IsSolution` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A380681–A380686, prime parameters and integral bilateral series*. URL: <https://oeis.org/A380681>.

*Commentary.*

The unpaginated Comments of OEIS A380681 state: "Conjecture: if F(x) satisfies p*x = Sum_{n=-oo..+oo} (-1)^n * x^(p*n) * (F(x) + x^n)^(p*n) with F(0) = 1 for some fixed integer p, then F(x) is an integer series in x iff p is prime. The g.f. A(x) of this sequence is the case when p = 2; other cases include A380682 (p=3), A380683 (p=5), A380684 (p=7), A380685 (p=11), and A380686 (p=13)." The constant coefficient is one. At degree N, the sum is over every integer j in [-K,K], for every K at least N+1. Thus the right side is p at degree one and zero at every other degree.

**Definition 1.3 (Existence and the prime criterion).**

$$claim = (\forall p: \mathbb{N}, (2 \le p) \implies ((\exists F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSolution}\left(p, F\right)) \land (\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSolution}\left(p, F\right)) \implies ((\forall n: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{coeff}\left(n, F\right) = (z: \mathbb{Q})) \iff (\operatorname{Nat}.\operatorname{Prime}\left(p\right))))))$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaPrimeBilateralIntegrality.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A380681–A380686, prime parameters and integral bilateral series*. URL: <https://oeis.org/A380681>.

*Commentary.*

The unpaginated Comments of OEIS A380681 state: "Conjecture: if F(x) satisfies p*x = Sum_{n=-oo..+oo} (-1)^n * x^(p*n) * (F(x) + x^n)^(p*n) with F(0) = 1 for some fixed integer p, then F(x) is an integer series in x iff p is prime. The g.f. A(x) of this sequence is the case when p = 2; other cases include A380682 (p=3), A380683 (p=5), A380684 (p=7), A380685 (p=11), and A380686 (p=13)." For each natural p at least two a normalized rational solution exists, and each normalized rational solution has all coefficients in the integers if and only if p is prime. Parameters at most zero are outside this statement.

**Theorem 1.4 (Prime parameters characterize integral solutions).**

$$\forall p: \mathbb{N}, (2 \le p) \implies ((\exists F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSolution}\left(p, F\right)) \land (\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSolution}\left(p, F\right)) \implies ((\forall n: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{coeff}\left(n, F\right) = (z: \mathbb{Q})) \iff (\operatorname{Nat}.\operatorname{Prime}\left(p\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/HannaPrimeBilateralIntegrality.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a380681-hanna-prime-bilateral-integrality` (proved) by `D5/S1/Recurrence/Bilateral/HannaPrimeBilateralIntegrality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a380681-hanna-prime-bilateral-integrality","declaration_gid":"D5/S1/Recurrence/Bilateral/HannaPrimeBilateralIntegrality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A380681–A380686, prime parameters and integral bilateral series*. URL: <https://oeis.org/A380681>.

*Commentary.*

Factoring the negative Laurent powers gives finite coefficient sums. At parameter one, a reindexing pairs the positive and negative binomial terms with opposite signs. Frobenius then makes every coefficient of the parameter-p sum divisible by p when p is prime. Removing its linear term gives a contraction by one coefficient degree; compatible iterates construct the normalized rational solution and prove its integrality at prime p. Below degree p, the equation reduces to the binomial expansion of (1-pX) to exponent -1/p. At a composite p, the least prime divisor divides the coefficient's factorial denominator and none of its numerator factors, contradicting integrality.

## References

- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaPrimeBilateralIntegrality.IsSolution`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaPrimeBilateralIntegrality.claim`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaPrimeBilateralIntegrality.result`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaPrimeBilateralIntegrality.term`
- Dependency: [D5/S1/Recurrence/Bilateral/BilateralProductModFour](BilateralProductModFour.md)
- Dependency: [D5/S1/Recurrence/Bilateral/HannaThetaFourModFour](HannaThetaFourModFour.md)
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](../Invariants/CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](../Invariants/PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](../Invariants/UnitReversionSquareParity.md)
- Dependency: [D5/S1/Recurrence/Residue/ContinuedFractionOddSquare](../Residue/ContinuedFractionOddSquare.md)
- Dependency: [D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime](../Residue/NegativePowerDiagonalModPrime.md)

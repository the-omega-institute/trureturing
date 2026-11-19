# Schulte's implicit quadrinomial power coefficients

## Abstract

The native integer series and all its power coefficients.

**Definition 1.1 (The native equation).**

$$\forall R: Type, [\operatorname{CommRing}\left(R\right)] \forall n: \mathbb{N}, \forall P: \operatorname{PowerSeries}\left(R\right), \operatorname{Native}\left(n, P\right) \iff P = 1 + X \cdot P^{n} + X^{2} \cdot P^{2 \cdot n} + X^{3} \cdot P^{3 \cdot n}$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/SchulteImplicitQuadrinomialPowers.Native` (`✓ std3`).

*Citation.* Werner Schulte (2015). *OEIS A262082: coefficients of powers of an implicit quadrinomial series*. URL: <https://oeis.org/A262082>.

*Commentary.*

For a commutative coefficient ring R, Native(n,P) means exactly P=1+X*P^n+X^2*P^(2*n)+X^3*P^(3*n) in R[[X]]. All exponents and indices are natural numbers.

**Theorem 1.2 (Every coefficient of every positive power).**

$$\forall n: \mathbb{N}, 1 \le n \Rightarrow \left(\operatorname{ExistsUnique}\left((fun P: \operatorname{PowerSeries}\left(\mathbb{Z}\right) \mapsto \operatorname{Native}\left(n, P\right))\right) \land \forall P: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{Native}\left(n, P\right) \Rightarrow \forall m: \mathbb{N}, 1 \le m \Rightarrow \forall k: \mathbb{N}, \operatorname{ratCast}\left(\operatorname{coeff}\left(k, P^{m}\right)\right) = \frac{m}{n \cdot k + m} \cdot \sum_{j = 0}^{k} (-2)^{j} \cdot \operatorname{binom}\left(n \cdot k + m, j\right) \cdot \operatorname{binom}\left(3 \cdot \left(n \cdot k + m\right) - 2 \cdot j, k - j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/SchulteImplicitQuadrinomialPowers.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a262082-schulte-power-coefficient` (proved) by `D5/S3/Combinatorics/PowerSeries/SchulteImplicitQuadrinomialPowers.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a262082-schulte-power-coefficient","declaration_gid":"D5/S3/Combinatorics/PowerSeries/SchulteImplicitQuadrinomialPowers.result","resolution_kind":"proved"} -->

*Citation.* Werner Schulte (2015). *OEIS A262082: coefficients of powers of an implicit quadrinomial series*. URL: <https://oeis.org/A262082>.

*Commentary.*

For every positive natural n there is exactly one integer formal power series satisfying the native equation. For every such series P, every positive natural m and every natural k, including zero, its degree-k coefficient in P^m, mapped into the rationals, equals the displayed sum. N abbreviates n*k+m and is positive. The sum includes j=0 and j=k. Both subtractions in binomial indices are natural truncated subtraction; binom(N,j)=0 for j>N. The prefactor and entire displayed sum are rational. There is no upper restriction on k. Coefficient agreement gives integer existence and uniqueness through the normalized contraction theorem. Set Q(t)=1+t+t^2+t^3 and U(y)=y*P(y^n). The equation becomes U=y*Q(U^n). Lagrange inversion at degree N and power m, followed by the expansion coefficient map and the quadrinomial coefficient identity, gives the formula. The polynomial identity's k<=3*N hypothesis follows from n>=1 and m>=1. The statement concerns formal coefficients; the source's separate lattice-path and logarithmic conjectures are outside it.

## References

- Truth anchor: `D5/S3/Combinatorics/PowerSeries/SchulteImplicitQuadrinomialPowers.Native`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/SchulteImplicitQuadrinomialPowers.result`
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](../../../S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/SchulteQuadrinomialAlternatingBinomialExpansion](../../../S1/Recurrence/SchulteQuadrinomialAlternatingBinomialExpansion.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo](../Nonnesting/NonnestingOneThreeTwoTwo.md)

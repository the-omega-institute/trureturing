# Hanna A300593 ordinary integrality

## Abstract

The square-exponential equations with cubic multipliers define a unique rational ordinary series with integral coefficients.

**Definition 1.1 (The normalized rational ordinary series).**

$$\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSource}\left(F\right)) \iff ((\operatorname{constantCoeff}\left(F\right) = 0) \land (\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, \operatorname{expSeries}\left(((n: \mathbb{Q}))^{2}, F\right)\right) = ((n: \mathbb{Q}))^{3} \cdot \operatorname{coeff}\left(n - 1, \operatorname{expSeries}\left(((n: \mathbb{Q}))^{2}, F\right)\right))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA300593Integrality.IsSource` (`✓ std3`).

*Citation.* Paul D. Hanna (2018). *OEIS A300593 square-exponential ordinary series and its A300592 companion*. URL: <https://oeis.org/A300593/internal>.

*Commentary.*

The constant coefficient of F is zero. For every positive natural n, the scalar inside the formal exponential is the rational square of n and the right-hand multiplier is the rational cube of n. Both extractions are ordinary coefficients. The formal exponential of tF is the substitution of C(t)F into PowerSeries.exp over the rationals.

**Definition 1.2 (The normalized A300592 companion).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsCompanion}\left(B\right)) \iff ((\operatorname{constantCoeff}\left(B\right) = 1) \land (\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, (B)^{(n)^{2}}\right) = ((n: \mathbb{Q}))^{3} \cdot \operatorname{coeff}\left(n - 1, (B)^{(n)^{2}}\right))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA300593Integrality.IsCompanion` (`✓ std3`).

*Citation.* Paul D. Hanna (2018). *OEIS A300593 square-exponential ordinary series and its A300592 companion*. URL: <https://oeis.org/A300593/internal>.

*Commentary.*

The companion B has constant coefficient one. Its natural power n squared satisfies an ordinary coefficient equation with multiplier n cubed at every positive natural n. The exponential generating function entries of B are eCoeff(B,r), the ordinary coefficient in degree r multiplied by r!.

**Theorem 1.3 (All-degree integrality and the exponential companion).**

$$(\exists F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSource}\left(F\right)) \land (\forall G: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSource}\left(G\right)) \implies (G = F))) \land (\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSource}\left(F\right)) \implies ((\forall m: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{coeff}\left(m, F\right) = (z: \mathbb{Q})) \land ((\operatorname{IsCompanion}\left(\operatorname{expSeries}\left(1, F\right)\right)) \land ((\operatorname{logOf}\left(\operatorname{expSeries}\left(1, F\right)\right) = F) \land ((\forall n: \mathbb{N}, \operatorname{expSeries}\left(((n: \mathbb{Q}))^{2}, F\right) = (\operatorname{expSeries}\left(1, F\right))^{(n)^{2}}) \land ((\forall B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsCompanion}\left(B\right)) \implies ((B = \operatorname{expSeries}\left(1, F\right)) \land (\operatorname{logOf}\left(B\right) = F))) \land (\operatorname{mk}\left((fun r: \mathbb{N} \mapsto \frac{\operatorname{eCoeff}\left(\operatorname{expSeries}\left(1, F\right), r\right)}{(\operatorname{factorial}\left(r\right): \mathbb{Q})})\right) = \operatorname{expSeries}\left(1, F\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA300593Integrality.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-a300593` (proved) by `D5/S1/Recurrence/Algebraic/HannaA300593Integrality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-a300593","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaA300593Integrality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A300593 square-exponential ordinary series and its A300592 companion*. URL: <https://oeis.org/A300593/internal>.

*Commentary.*

Triangular existence and uniqueness apply to the separate scalar functions n squared and n cubed. Strong induction takes the lower ordinary coefficients as integers, forms their strict prefix P, and transfers all lower equations to P by coefficient agreement. For a prime coprime to n, MarkedAssemblyExtraMarker treats two ambient markers on every block and an extra ambient marker on the pointed object. Its signed fixed-point sums give the full Sylow-order divisibility of the factorial-weighted residual. The coefficient at degree n is the negative residual divided by n squared, a local unit. For a prime dividing n, write s for the valuation of n. The exponential prefix estimate bounds the valuation of n times the previous exponential coefficient below by 3s and that of the current exponential coefficient divided by n squared below by 2s minus 1, whenever the respective terms are nonzero. Thus a prime dividing a reduced denominator is ruled out in either case. The normalization covers degree zero. The formal power law holds for every natural exponent index, including zero. The formal exponential and logarithm give both companion correspondences. Dividing the EGF entries by their factorials reconstructs B in every degree.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300593Integrality.IsCompanion`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300593Integrality.IsSource`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300593Integrality.result`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaA300591RationalModel](HannaA300591RationalModel.md)
- Dependency: [D5/S1/Recurrence/Algebraic/MarkedAssemblyExtraMarker](MarkedAssemblyExtraMarker.md)
- Dependency: [D5/S1/Recurrence/Residue/IntegralEGFComposition](../Residue/IntegralEGFComposition.md)

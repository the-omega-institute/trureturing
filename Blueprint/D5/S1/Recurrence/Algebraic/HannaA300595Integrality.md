# Hanna A300595: ordinary integrality

## Abstract

The cubic exponential coefficient equations have a unique normalized rational ordinary series, and every positive ordinary coefficient is an integer.

**Definition 1.1 (The normalized rational ordinary series).**

$$\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSource}\left(F\right)) \iff ((\operatorname{constantCoeff}\left(F\right) = 0) \land (\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, \operatorname{expSeries}\left(((n: \mathbb{Q}))^{3}, F\right)\right) = ((n: \mathbb{Q}))^{3} \cdot \operatorname{coeff}\left(n - 1, \operatorname{expSeries}\left(((n: \mathbb{Q}))^{3}, F\right)\right))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA300595Integrality.IsSource` (`✓ std3`).

*Citation.* Paul D. Hanna (2018). *OEIS A300595 cubic-exponential ordinary series*. URL: <https://oeis.org/A300595>.

*Commentary.*

The ambient series ring is Q[[x]]. The constant coefficient is zero. For every natural n>=1, the scalar is the rational cube of n, and both extractions are ordinary coefficients. The subtraction n-1 is used only in this positive-index domain. This is the normalized ordinary generating function specified by OEIS A300595 NAME and OFFSET; no integrality condition is included in its definition. Formal exp(t F) uses HannaA300591RationalModel.expSeries t F, namely substitution of C(t)F into PowerSeries.exp Q. All substitutions used below have zero constant input.

**Definition 1.2 (The normalized A300594 companion).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsCompanion}\left(B\right)) \iff ((\operatorname{constantCoeff}\left(B\right) = 1) \land (\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, (B)^{(n)^{3}}\right) = ((n: \mathbb{Q}))^{3} \cdot \operatorname{coeff}\left(n - 1, (B)^{(n)^{3}}\right))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA300595Integrality.IsCompanion` (`✓ std3`).

*Citation.* Paul D. Hanna (2018). *OEIS A300595 cubic-exponential ordinary series*. URL: <https://oeis.org/A300595>.

*Commentary.*

The companion B has constant coefficient one. Its natural power n^3 satisfies the displayed ordinary coefficient equation for every n>=1. A300594 presents B as an exponential generating function, with entries beta(r)=r! times its ordinary degree-r coefficient, for every r>=0. This convention applies to B alone. The coefficients of A300595 remain the unscaled ordinary coefficients of F=log(B). The companion's integer wording is not an assumption.

**Theorem 1.3 (The complete cubic source event).**

$$(\exists F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSource}\left(F\right)) \land (\forall G: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSource}\left(G\right)) \implies (G = F))) \land (\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSource}\left(F\right)) \implies ((\forall m: \mathbb{N}, (1 \le m) \implies (\exists z: \mathbb{Z}, \operatorname{coeff}\left(m, F\right) = (z: \mathbb{Q}))) \land ((\operatorname{IsCompanion}\left(\operatorname{expSeries}\left(1, F\right)\right)) \land ((\operatorname{logOf}\left(\operatorname{expSeries}\left(1, F\right)\right) = F) \land ((\forall n: \mathbb{N}, \operatorname{expSeries}\left(((n: \mathbb{Q}))^{3}, F\right) = (\operatorname{expSeries}\left(1, F\right))^{(n)^{3}}) \land ((\forall B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsCompanion}\left(B\right)) \implies (B = \operatorname{expSeries}\left(1, F\right))) \land (\operatorname{mk}\left((fun r: \mathbb{N} \mapsto \frac{\operatorname{eCoeff}\left(\operatorname{expSeries}\left(1, F\right), r\right)}{(\operatorname{factorial}\left(r\right): \mathbb{Q})})\right) = \operatorname{expSeries}\left(1, F\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA300595Integrality.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-a300595` (proved) by `D5/S1/Recurrence/Algebraic/HannaA300595Integrality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-a300595","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaA300595Integrality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A300595 cubic-exponential ordinary series*. URL: <https://oeis.org/A300595>.

*Commentary.*

The first conjunct proves existence and uniqueness among all normalized rational solutions of the source identity. It uses the rational model's triangular_exists_unique with both scalar functions equal to n^3; their nonvanishing follows from n>=1. This rational construction precedes every integrality argument. The second conjunct applies to every rational source F and every positive natural m, and supplies an integer equal to its ordinary coefficient. The zero coefficient is already zero by IsSource. No integral ambient object, cutoff, sign assumption or rescaling is used. The result also proves the normalized companion, log(exp(F))=F, exp(n^3 F)=exp(F)^(n^3) for every natural n including zero, uniqueness of every normalized companion B, and reconstruction of exp(F) from eCoeff(exp(F),r)/r! in every degree r>=0. Formal exp/log inverses and the exponential power identity are reused from their actual owners. Thus the primary ordinary definition and the companion EGF/log convention describe the same unique rational object. The illustrative source programs and the separate displayed recurrence supply no arithmetic premise here. The integrality induction uses the actual strict integral prefix. Coefficient agreement transfers every lower cubic equation to that prefix. At primes not dividing the index, MarkedAssemblyCoefficients with three independent marker coordinates proves local integrality of the residual by the full Sylow order, with the original ambient marker set retained after root removal. Division by the cube is a local unit. At primes dividing the index, local_automatic_bound applies to the cube and the strict local prefix. The factorial valuation estimate gives a nonnegative coefficient valuation, including the prime two. A nonintegral rational coefficient would have a prime dividing its reduced denominator, contradicting these two exhaustive cases. The degree-one identity forces coefficient one directly, and strong induction covers every subsequent index.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300595Integrality.IsCompanion`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300595Integrality.IsSource`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300595Integrality.result`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaA300591RationalModel](HannaA300591RationalModel.md)
- Dependency: [D5/S1/Recurrence/Algebraic/MarkedAssemblyCoefficients](MarkedAssemblyCoefficients.md)
- Dependency: [D5/S1/Recurrence/Residue/IntegralEGFComposition](../Residue/IntegralEGFComposition.md)

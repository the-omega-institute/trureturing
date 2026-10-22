# Cullinan--Young Krawtchouk Sign Interpolant

## Abstract

The even Krawtchouk sign interpolant has the leading coefficient stated by Cullinan and Young.

The source uses the nodes j minus N/2 and the Lagrange basis ell_i. The proposition spells out the interpolation sum and its basis products over rational nodes.

**Definition 1.1 (Lagrange basis polynomial).**

$$\forall N \in \mathbb{N},\; \forall i \in \mathbb{N},\; \operatorname{ell}\left(N, i\right) = \prod_{j \in \operatorname{Finset}.\operatorname{erase}\left(\operatorname{Finset}.\operatorname{range}\left(N + 1\right), i\right)} (\operatorname{Polynomial}.\operatorname{C}\left(\frac{1}{(i: \mathbb{Q}) - (j: \mathbb{Q})}\right) \cdot (X - \operatorname{Polynomial}.\operatorname{C}\left((j: \mathbb{Q}) - \frac{(N: \mathbb{Q})}{2}\right)))$$

*Formalization.* `D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk.ell` (`✓ std3`).

*Citation.* J. Cullinan and E. Young (2026). *The Gibbs phenomenon for the Krawtchouk polynomials*. DOI: [10.1007/s10958-026-08499-9](https://doi.org/10.1007/s10958-026-08499-9). URL: <https://arxiv.org/abs/2603.05408v1>.

*Commentary.*

For natural N and i, ell is the product of the centered linear factors at all nodes except i, with the corresponding rational denominator.

**Definition 1.2 (Krawtchouk sign interpolant).**

$$\forall N \in \mathbb{N},\; \operatorname{I}\left(N\right) = \sum_{i \in \operatorname{Finset}.\operatorname{range}\left(N + 1\right)} (\operatorname{Polynomial}.\operatorname{C}\left((\operatorname{SignType}.\operatorname{sign}\left((i: \mathbb{Q}) - \frac{(N: \mathbb{Q})}{2}\right): \mathbb{Q})\right) \cdot \operatorname{ell}\left(N, i\right))$$

*Formalization.* `D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk.I` (`✓ std3`).

*Citation.* J. Cullinan and E. Young (2026). *The Gibbs phenomenon for the Krawtchouk polynomials*. DOI: [10.1007/s10958-026-08499-9](https://doi.org/10.1007/s10958-026-08499-9). URL: <https://arxiv.org/abs/2603.05408v1>.

*Commentary.*

For natural N, I is the sum of the sign values at the centered nodes multiplied by the corresponding Lagrange basis polynomials.

**Definition 1.3 (Remark 8 leading coefficient formula).**

$$claim \Leftrightarrow (\forall N \in \mathbb{N},\; ((2 \le N)) \Rightarrow (((\operatorname{Even}\left(N\right))) \Rightarrow (\operatorname{Polynomial}.\operatorname{leadingCoeff}\left(\operatorname{I}\left(N\right)\right) = \frac{(-1)^{(\operatorname{Nat}.\operatorname{div}\left(N - 2, 2\right))} \cdot (\operatorname{catalan}\left(\operatorname{Nat}.\operatorname{div}\left(N - 2, 2\right)\right): \mathbb{Q})}{(\operatorname{Nat}.\operatorname{factorial}\left(N - 1\right): \mathbb{Q})})))$$

*Formalization.* `D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk.claim` (`✓ std3`).

*Citation.* J. Cullinan and E. Young (2026). *The Gibbs phenomenon for the Krawtchouk polynomials*. DOI: [10.1007/s10958-026-08499-9](https://doi.org/10.1007/s10958-026-08499-9). URL: <https://arxiv.org/abs/2603.05408v1>.

*Commentary.*

Page 6, Remark 8 states: "Numerical experimentation suggests that the leading coefficient of I_N(x) (and, therefore, F_N(x)) is given by (−1)^{(N−2)/2}/(N−1)! · C((N−2)/2), where C(n) is the nth Catalan number." The source takes N even. The Lean statement encodes the even case with N at least two; natural division is rendered by Nat.div and the coefficient is rational. Page 6 defines: "Let I_N(x) be the Lagrange form of the interpolating polynomial of the points of P_N. Then I_N(x) = Σ_{i=0}^{N} sgn(i − N/2) ℓ_i(x), where ℓ_i(x) = Π_{j=0,j≠i}^{N} (x − (j − N/2))/(i − j)." The interpolation sum and the basis products appear directly in the formula below.

**Theorem 1.4 (The proved leading coefficient formula).**

$$\forall N \in \mathbb{N},\; ((2 \le N)) \Rightarrow (((\operatorname{Even}\left(N\right))) \Rightarrow (\operatorname{Polynomial}.\operatorname{leadingCoeff}\left(\operatorname{I}\left(N\right)\right) = \frac{(-1)^{(\operatorname{Nat}.\operatorname{div}\left(N - 2, 2\right))} \cdot (\operatorname{catalan}\left(\operatorname{Nat}.\operatorname{div}\left(N - 2, 2\right)\right): \mathbb{Q})}{(\operatorname{Nat}.\operatorname{factorial}\left(N - 1\right): \mathbb{Q})}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk.result` (`✓ std3`). ∎

*Resolves.* `Problems/cullinan-young-2026-krawtchouk-sign-leading-coefficient-remark-8` (proved) by `D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cullinan-young-2026-krawtchouk-sign-leading-coefficient-remark-8","declaration_gid":"D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* J. Cullinan and E. Young (2026). *The Gibbs phenomenon for the Krawtchouk polynomials*. DOI: [10.1007/s10958-026-08499-9](https://doi.org/10.1007/s10958-026-08499-9). URL: <https://arxiv.org/abs/2603.05408v1>.

*Commentary.*

The proof uses Vieta's next-coefficient identity, reflection of the centered nodes, alternating partial binomial sums, and the Catalan central-binomial identity. The nonzero next coefficient also gives degree 2m plus 1 for N equal to 2(m plus 1).

The statement covers every even N at least two. The source's identification of F_N with I_N is Proposition 6 and is not asserted here; odd N is outside the source observation.

## References

- Truth anchor: `D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk.I`
- Truth anchor: `D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk.claim`
- Truth anchor: `D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk.ell`
- Truth anchor: `D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk.result`

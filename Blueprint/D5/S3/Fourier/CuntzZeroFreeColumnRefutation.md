# Cuntz's zero-free column question

## Abstract

Every zero-free column of an integral Fourier matrix consists of integer units.

**Definition 1.1 (Integral Fourier matrix equations).**

$$\forall n \in \mathbb{N},\; \forall hn \in 0 < n,\; \forall s \in Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{Z}\right),\; \forall d \in Fin\left(n\right) \to \mathbb{R},\; FourierAxioms\left(hn, s, d\right) \Leftrightarrow (\forall i \in Fin\left(n\right),\; s\left(i, \operatorname{Fin}.\operatorname{mk}\left(0, hn\right)\right) = 1)\land (\operatorname{Matrix}.\operatorname{det}\left(s\right) \ne 0)\land (\forall i \in Fin\left(n\right),\; 0 < \operatorname{Real}.\operatorname{sqrt}\left(d\left(i\right)\right))\land (\operatorname{Matrix}.\operatorname{map}\left(s, (\operatorname{Int}.\operatorname{cast}: \mathbb{Z} \to \mathbb{R})\right) \cdot \operatorname{Matrix}.\operatorname{transpose}\left(\operatorname{Matrix}.\operatorname{map}\left(s, (\operatorname{Int}.\operatorname{cast}: \mathbb{Z} \to \mathbb{R})\right)\right) = \operatorname{Matrix}.\operatorname{diagonal}\left(d\right))\land (\forall i \in Fin\left(n\right),\; \forall j \in Fin\left(n\right),\; \operatorname{Real}.\operatorname{sqrt}\left(d\left(j\right)\right) \cdot (s\left(i, j\right): \mathbb{R}) = \operatorname{Real}.\operatorname{sqrt}\left(d\left(i\right)\right) \cdot (s\left(j, i\right): \mathbb{R}))\land (\forall i \in Fin\left(n\right),\; \forall j \in Fin\left(n\right),\; \forall l \in Fin\left(n\right),\; \exists z \in \mathbb{Z},\; \sum_{k: Fin\left(n\right)} (\frac{(s\left(k, i\right): \mathbb{R}) \cdot (s\left(k, j\right): \mathbb{R}) \cdot (s\left(k, l\right): \mathbb{R})}{d\left(k\right)}) = (z: \mathbb{R}))$$

*Formalization.* `D5/S3/Fourier/CuntzZeroFreeColumnRefutation.FourierAxioms` (`✓ std3`).

*Citation.* Michael Cuntz (2009). *Integral modular data and congruences*. DOI: [10.1007/s10801-008-0139-y](https://doi.org/10.1007/s10801-008-0139-y). URL: <https://arxiv.org/abs/math/0611233v2>.

*Commentary.*

Definition 4.1 (arXiv v2, pp. 8–9) starts: “Let s be an integral Fourier matrix, i.e. s ∈ ℤ^{n×n} and” and lists the four equations displayed here. Definition 3.1 (pp. 3–4) states: “Here, √dᵢ is chosen greater than 0.” The source indices 1,…,n are Fin n, with source index 1 represented by Fin.mk 0 hn. The matrix equation fixes d as the row norms; the explanatory reversed-index sum in Definition 3.1 is not an additional equation. Each structure constant is the displayed real sum equal to an integer.

**Definition 1.2 (Integral Fourier matrices).**

$$\forall n \in \mathbb{N},\; \forall hn \in 0 < n,\; \forall s \in Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{Z}\right),\; IsIntegralFourierMatrix\left(hn, s\right) \Leftrightarrow \left(\exists d \in Fin\left(n\right) \to \mathbb{R},\; FourierAxioms\left(hn, s, d\right)\right)$$

*Formalization.* `D5/S3/Fourier/CuntzZeroFreeColumnRefutation.IsIntegralFourierMatrix` (`✓ std3`).

*Citation.* Michael Cuntz (2009). *Integral modular data and congruences*. DOI: [10.1007/s10801-008-0139-y](https://doi.org/10.1007/s10801-008-0139-y). URL: <https://arxiv.org/abs/math/0611233v2>.

*Commentary.*

Definition 4.1 (arXiv v2, pp. 8–9): “Let s be an integral Fourier matrix, i.e. s ∈ ℤ^{n×n} and” is followed by conditions (1)–(4). The real function d supplies the diagonal entries and positive square roots. Existence of a T-matrix and the later congruence conditions are not required.

**Definition 1.3 (Section 7, Question (5)).**

$$claim \Leftrightarrow \left(\exists n \in \mathbb{N},\; \exists hn \in 0 < n,\; \exists s \in Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{Z}\right),\; (IsIntegralFourierMatrix\left(hn, s\right))\land (\exists k \in Fin\left(n\right),\; (\forall i \in Fin\left(n\right),\; s\left(i, k\right) \ne 0)\land (\exists i \in Fin\left(n\right),\; (s\left(i, k\right) \ne 1)\land (s\left(i, k\right) \ne -1)))\right)$$

*Formalization.* `D5/S3/Fourier/CuntzZeroFreeColumnRefutation.claim` (`✓ std3`).

*Citation.* Michael Cuntz (2009). *Integral modular data and congruences*. DOI: [10.1007/s10801-008-0139-y](https://doi.org/10.1007/s10801-008-0139-y). URL: <https://arxiv.org/abs/math/0611233v2>.

*Commentary.*

Section 7(5) (arXiv v2, p. 21; journal p. 380): “Does an integral Fourier matrix s exist with a column k such that ∀i sᵢₖ ≠ 0 and ∃i sᵢₖ ≠ ±1?” The formula quantifies every positive size n, matrix s, column k and row i. The nonunit condition is the conjunction s i k ≠ 1 and s i k ≠ −1.

**Theorem 1.4 (The answer is negative).**

$$\neg (\exists n \in \mathbb{N},\; \exists hn \in 0 < n,\; \exists s \in Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{Z}\right),\; (IsIntegralFourierMatrix\left(hn, s\right))\land (\exists k \in Fin\left(n\right),\; (\forall i \in Fin\left(n\right),\; s\left(i, k\right) \ne 0)\land (\exists i \in Fin\left(n\right),\; (s\left(i, k\right) \ne 1)\land (s\left(i, k\right) \ne -1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CuntzZeroFreeColumnRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/cuntz2009` (refuted) by `D5/S3/Fourier/CuntzZeroFreeColumnRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cuntz2009","declaration_gid":"D5/S3/Fourier/CuntzZeroFreeColumnRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Michael Cuntz (2009). *Integral modular data and congruences*. DOI: [10.1007/s10801-008-0139-y](https://doi.org/10.1007/s10801-008-0139-y). URL: <https://arxiv.org/abs/math/0611233v2>.

*Commentary.*

For the real matrix A obtained from s, A A.transpose = Matrix.diagonal d implies that A.transpose times the inverse diagonal times A is one. Its diagonal entries give ∑ᵢ sᵢₖ²/dᵢ = 1. The first column gives ∑ᵢ 1/dᵢ = 1. Every nonzero integer square is at least one, and positivity of all reciprocal norms forces equality term by term. Thus every entry in a zero-free column is 1 or −1. The argument applies to any square integer matrix with first column one and positive orthogonal row norms; determinant, symmetrization and fusion integrality are unnecessary.

## References

- Truth anchor: `D5/S3/Fourier/CuntzZeroFreeColumnRefutation.FourierAxioms`
- Truth anchor: `D5/S3/Fourier/CuntzZeroFreeColumnRefutation.IsIntegralFourierMatrix`
- Truth anchor: `D5/S3/Fourier/CuntzZeroFreeColumnRefutation.claim`
- Truth anchor: `D5/S3/Fourier/CuntzZeroFreeColumnRefutation.result`

# An order-six unimodular zerofree matrix with both maxima three

## Abstract

An explicit integer matrix refutes Finch's order-six zerofree conjecture.

**Definition 1.1 (Integer matrices).**

$$\forall (n : \mathbb{N}), (\operatorname{IntegerMatrix}\left(n\right) = \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{Z}\right))$$

*Formalization.* `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.IntegerMatrix` (`✓ std3`).

*Citation.* Steven Finch (2026). *Small Matrices with Small Inverses: Unimodular Zerofree Cases*. DOI: [10.48550/arXiv.2605.03691](https://doi.org/10.48550/arXiv.2605.03691). URL: <https://arxiv.org/abs/2605.03691v4>.

*Commentary.*

The source defines “an n×n integer matrix M” with indices 0 through n−1. The carrier is Matrix (Fin n) (Fin n) ℤ.

**Definition 1.2 (Maximum absolute entry).**

$$\forall (n : \mathbb{N}), (\forall (M : \operatorname{IntegerMatrix}\left(n\right)), (\operatorname{maxAbsEntry}\left(M\right) = \operatorname{Finset}.\operatorname{sup}\left((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right)), (\operatorname{fun} ij \mapsto \operatorname{Int}.\operatorname{natAbs}\left(M\left(ij.1, ij.2\right)\right))\right)))$$

*Formalization.* `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.maxAbsEntry` (`✓ std3`).

*Citation.* Steven Finch (2026). *Small Matrices with Small Inverses: Unimodular Zerofree Cases*. DOI: [10.48550/arXiv.2605.03691](https://doi.org/10.48550/arXiv.2605.03691). URL: <https://arxiv.org/abs/2605.03691v4>.

*Commentary.*

The source uses the maximum absolute entry of M; the displayed finite supremum applies Int.natAbs to all coordinate pairs.

**Definition 1.3 (Unimodular matrices).**

$$\forall (n : \mathbb{N}), (\forall (M : \operatorname{IntegerMatrix}\left(n\right)), (\operatorname{Unimodular}\left(M\right) = \operatorname{IsUnit}\left(\operatorname{Matrix}.\operatorname{det}\left(M\right)\right)))$$

*Formalization.* `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.Unimodular` (`✓ std3`).

*Citation.* Steven Finch (2026). *Small Matrices with Small Inverses: Unimodular Zerofree Cases*. DOI: [10.48550/arXiv.2605.03691](https://doi.org/10.48550/arXiv.2605.03691). URL: <https://arxiv.org/abs/2605.03691v4>.

*Commentary.*

An n×n integer matrix M with determinant ±1 is called unimodular.

**Definition 1.4 (The source's alpha).**

$$\forall (n : \mathbb{N}), (\forall (M : \operatorname{IntegerMatrix}\left(n\right)), (\operatorname{alpha}\left(M\right) = \operatorname{maxAbsEntry}\left(M\right)))$$

*Formalization.* `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.alpha` (`✓ std3`).

*Citation.* Steven Finch (2026). *Small Matrices with Small Inverses: Unimodular Zerofree Cases*. DOI: [10.48550/arXiv.2605.03691](https://doi.org/10.48550/arXiv.2605.03691). URL: <https://arxiv.org/abs/2605.03691v4>.

*Commentary.*

The source sets α=‖M‖, the maximum absolute entry of M.

**Definition 1.5 (The source's beta).**

$$\forall (n : \mathbb{N}), (\forall (M : \operatorname{IntegerMatrix}\left(n\right)), (\operatorname{beta}\left(M\right) = \operatorname{Finset}.\operatorname{sup}\left((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right)), (\operatorname{fun} ij \mapsto \operatorname{Int}.\operatorname{natAbs}\left(\left(M^{-1}\right)\left(ij.1, ij.2\right)\right))\right)))$$

*Formalization.* `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.beta` (`✓ std3`).

*Citation.* Steven Finch (2026). *Small Matrices with Small Inverses: Unimodular Zerofree Cases*. DOI: [10.48550/arXiv.2605.03691](https://doi.org/10.48550/arXiv.2605.03691). URL: <https://arxiv.org/abs/2605.03691v4>.

*Commentary.*

The source sets β=‖M⁻¹‖, the maximum absolute entry of M⁻¹.

**Definition 1.6 (Zerofree matrices).**

$$\forall (n : \mathbb{N}), (\forall (M : \operatorname{IntegerMatrix}\left(n\right)), (\operatorname{Zerofree}\left(M\right) = \left((\forall (i : \operatorname{Fin}\left(n\right)), (\forall (j : \operatorname{Fin}\left(n\right)), (M\left(i, j\right) \ne 0))) \land (\forall (i : \operatorname{Fin}\left(n\right)), (\forall (j : \operatorname{Fin}\left(n\right)), (\left(M^{-1}\right)\left(i, j\right) \ne 0)))\right)))$$

*Formalization.* `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.Zerofree` (`✓ std3`).

*Citation.* Steven Finch (2026). *Small Matrices with Small Inverses: Unimodular Zerofree Cases*. DOI: [10.48550/arXiv.2605.03691](https://doi.org/10.48550/arXiv.2605.03691). URL: <https://arxiv.org/abs/2605.03691v4>.

*Commentary.*

The source calls M zerofree if none of the entries in M and none of the entries in M⁻¹ are zero.

**Definition 1.7 (Finch's Conjecture 4).**

$$\operatorname{claim} \Leftrightarrow (\forall (M : \operatorname{IntegerMatrix}\left(6\right)), ((\operatorname{Unimodular}\left(M\right)) \Rightarrow ((\operatorname{Zerofree}\left(M\right)) \Rightarrow ((\operatorname{alpha}\left(M\right) = 3) \Rightarrow ((\operatorname{beta}\left(M\right) = 3) \Rightarrow (\operatorname{False}))))))$$

*Formalization.* `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.claim` (`✓ std3`).

*Citation.* Steven Finch (2026). *Small Matrices with Small Inverses: Unimodular Zerofree Cases*. DOI: [10.48550/arXiv.2605.03691](https://doi.org/10.48550/arXiv.2605.03691). URL: <https://arxiv.org/abs/2605.03691v4>.

*Commentary.*

Conjecture 4, printed and PDF page 7: “No 6×6 matrices exist that are tied to α=β=3.”

Introduction, printed pages 1–2: “An n×n integer matrix M with determinant ±1 is called unimodular. Let α=‖M‖ and β=‖M⁻¹‖, the maximum absolute entry of M and M⁻¹, respectively.”

The same introduction states: “The matrix M is called zerofree if none of the entries in M and none of the entries in M⁻¹ are zero. (Involving both matrices in this definition is somewhat unorthodox.) Our interest is in unimodular zerofree matrices for which both α and β are small.”

Here M ranges over all six by six integer matrices. The named predicates and maxima are the definitions displayed above; the inverse is Mathlib's nonsingular matrix inverse.

**Theorem 1.8 (Conjecture 4 is false).**

$$\neg (\forall (M : \operatorname{IntegerMatrix}\left(6\right)), ((\operatorname{Unimodular}\left(M\right)) \Rightarrow ((\operatorname{Zerofree}\left(M\right)) \Rightarrow ((\operatorname{alpha}\left(M\right) = 3) \Rightarrow ((\operatorname{beta}\left(M\right) = 3) \Rightarrow (\operatorname{False}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/finch-unimodular-zerofree-six` (refuted) by `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"finch-unimodular-zerofree-six","declaration_gid":"D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Steven Finch (2026). *Small Matrices with Small Inverses: Unimodular Zerofree Cases*. DOI: [10.48550/arXiv.2605.03691](https://doi.org/10.48550/arXiv.2605.03691). URL: <https://arxiv.org/abs/2605.03691v4>.

*Commentary.*

Take the integer matrix whose rows are (3,2,2,2,2,2), (2,3,2,2,2,2), (2,2,3,2,2,2), (2,2,2,1,2,2), (2,2,2,2,1,2), and (2,2,2,2,2,1). Its integral inverse has rows (-1,-2,-2,2,2,2), (-2,-1,-2,2,2,2), (-2,-2,-1,2,2,2), (2,2,2,-3,-2,-2), (2,2,2,-2,-3,-2), and (2,2,2,-2,-2,-3). Their product is the identity. Mathlib's right-inverse and determinant-unit theorems identify this inverse and establish unimodularity. Every entry of both matrices is nonzero and both finite absolute maxima are three.

The cancellation between three positive and three negative diagonal signs gives the displayed small integral inverse. The theorem establishes the single order-six counterexample. A symbolic family in every positive even dimension, exhaustive orbit classification, the separate case α=β=2, and odd-dimensional nonexistence statements remain separate questions. The source's subsequent discussion uses no theorem conditional on Conjecture 4.

## References

- Truth anchor: `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.IntegerMatrix`
- Truth anchor: `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.Unimodular`
- Truth anchor: `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.Zerofree`
- Truth anchor: `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.alpha`
- Truth anchor: `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.beta`
- Truth anchor: `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.claim`
- Truth anchor: `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.maxAbsEntry`
- Truth anchor: `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.result`

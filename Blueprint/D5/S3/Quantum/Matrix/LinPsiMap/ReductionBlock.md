# The map Psi and reduction-block positivity

## Abstract

Reduction of a positive block supplies the reflected spectral comparison.

**Definition 1.1 (The trace reflection map).**

Lean statement: `D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock.psi`

*Formalization.* `D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock.psi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *New properties for certain positive semidefinite matrices*. DOI: [10.48550/arXiv.1609.08231](https://doi.org/10.48550/arXiv.1609.08231). URL: <https://arxiv.org/abs/1609.08231v1>.

*Commentary.*

For every complex square matrix T, define Psi(T)=2 trace(T) I−T. The reduction map R(T)=trace(T) I−T is the related map used to construct the positive block in the argument.

**Definition 1.2 (Antisymmetric matrix units).**

$$\forall (n: \mathbb{N}), \forall (k: \operatorname{Fin}\left(n\right)), \forall (l: \operatorname{Fin}\left(n\right)), \operatorname{skew}\left(k, l\right) = \operatorname{Matrix.single}\left(k, l, (1: \mathbb{C})\right) - \operatorname{Matrix.single}\left(l, k, (1: \mathbb{C})\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock.skew` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For indices k and l in Fin n, subtract the matrix unit at (l,k) from the matrix unit at (k,l). This gives an antisymmetric complex matrix, which is zero when k equals l.

**Theorem 1.3 (The sum of antisymmetric congruences).**

$$\forall (n: \mathbb{N}), \forall (T: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{HSMul.hSMul}\left(\operatorname{Complex.ofReal}\left((\frac{1}{2}: \mathbb{R})\right), (\sum_{(k: \operatorname{Fin}\left(n\right))} \sum_{(l: \operatorname{Fin}\left(n\right))} \operatorname{skew}\left(k, l\right) \cdot T \cdot \operatorname{Matrix.conjTranspose}\left(\operatorname{skew}\left(k, l\right)\right))\right) = \operatorname{HSMul.hSMul}\left(\operatorname{Matrix.trace}\left(T\right), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right))\right) - \operatorname{Matrix.transpose}\left(T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock.skew_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex square matrix T, one half of the sum of skew(k,l) T skew(k,l)-adjoint over all ordered pairs equals trace(T) times the identity minus the transpose of T. The identity holds without symmetry or positivity assumptions on T.

**Theorem 1.4 (Positivity of the reduction block).**

Lean statement: `D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock.reduction_block_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock.reduction_block_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *New properties for certain positive semidefinite matrices*. DOI: [10.48550/arXiv.1609.08231](https://doi.org/10.48550/arXiv.1609.08231). URL: <https://arxiv.org/abs/1609.08231v1>.

*Commentary.*

Let the complex block matrix [A X; X-adjoint B] be positive semidefinite. Then [R(A) R(X-adjoint); R(X) R(B)] is positive semidefinite, in every finite dimension and without commutation or rank assumptions.

For coordinate indices k and l, form the antisymmetric matrix F from the two matrix units at (k,l) and (l,k). One half of the sum of F T F-adjoint over all ordered pairs is trace(T) I−transpose(T). Apply these congruences simultaneously in both diagonal blocks to the transpose of the original positive block. The resulting positive sum has exactly the stated four blocks.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock.psi`
- Truth anchor: `D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock.reduction_block_posSemidef`
- Truth anchor: `D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock.skew`
- Truth anchor: `D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock.skew_sum`
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound](../LinGProperty/ArithmeticBound.md)

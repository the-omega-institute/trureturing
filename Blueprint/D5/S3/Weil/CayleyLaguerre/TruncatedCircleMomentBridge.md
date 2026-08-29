# Truncated Circle Moment Bridge

## Abstract

Every positive semidefinite Hermitian truncated Toeplitz moment vector has a finite atomic representing measure on the complex unit circle.

**Theorem 1.1 (Truncated positive Toeplitz moments have a circle representation).**

$$\forall N \in \mathbb{N}, r \in \mathbb{Z} \to \mathbb{C},\; \left(\left(\forall ell \in \mathbb{Z},\; r\left(\operatorname{neg}\left(ell\right)\right) = \operatorname{star}\left(r\left(ell\right)\right)\right) \land \operatorname{PosSemidef}\left(\operatorname{Matrix}\left((j,k\in\operatorname{Fin}\left(N + 1\right) \mapsto r\left(\operatorname{toInt}\left(j\right) - \operatorname{toInt}\left(k\right)\right))\right)\right)\right) \Rightarrow \left(\exists sigma \in \operatorname{FiniteMeasure}\left(\operatorname{Circle}\left(\right)\right),\; \forall ell \in \mathbb{Z},\; \operatorname{natAbs}\left(ell\right) \le N \Rightarrow \operatorname{integral}\left(z, \operatorname{Circle}\left(\right), \operatorname{zpow}\left(z, \operatorname{neg}\left(ell\right)\right), sigma\right) = r\left(ell\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CayleyLaguerre/TruncatedCircleMomentBridge.truncated_circle_moment_of_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Gram factorization realizes the truncated Toeplitz matrix as inner products of a finite vector orbit. The one-step shift descends through the Gram kernel and completes to a unitary operator.

The commuting self-adjoint real and imaginary parts admit a joint orthogonal eigenspace decomposition. Their joint spectral points lie on the complex unit circle and the squared orbit coefficients form the required finite atomic measure.

## References

- Truth anchor: `D5/S3/Weil/CayleyLaguerre/TruncatedCircleMomentBridge.truncated_circle_moment_of_posSemidef`
- Dependency: [D5/S3/Weil/TestFunctions/ToeplitzContactSupport](../TestFunctions/ToeplitzContactSupport.md)

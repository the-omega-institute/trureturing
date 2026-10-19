# Gaussian entropy-gap representation

## Abstract

Diagonal determinant-integral subentropy equals an integrable Gaussian entropy Jensen gap.

Let p be a probability vector on a finite type I. Under the product of independent standard real Gaussian laws indexed by I×{0,1}, put X_i(z)=(z_(i,0)^2+z_(i,1)^2)/2 and a(z)=Σ_i p_i X_i(z). Write η(u)=−u log u, with η(0)=0. The entire gap η(a)−Σ_i p_i η(X_i) is integrable.

**Theorem 1.1 (The exact diagonal Gaussian representation).**

$$\operatorname{Integrable}\left(\operatorname{eta}\left(a\right) - \operatorname{sum}\left(\operatorname{p}\left(i\right) \cdot \operatorname{eta}\left(\operatorname{X}\left(i\right)\right)\right), gamma\right) \land \operatorname{Q}\left(\operatorname{diag}\left(p\right)\right) = \operatorname{E}\left(\operatorname{eta}\left(a\right) - \operatorname{sum}\left(\operatorname{p}\left(i\right) \cdot \operatorname{eta}\left(\operatorname{X}\left(i\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/GaussianEntropy.diagonal_subentropy_gaussian_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scalar Laplace-Jensen identity represents the gap by the nonnegative kernel [Σ_i p_i exp(−sX_i)−exp(−sa)]/s². Each exponential is bounded by one and is integrable. The Gaussian coordinate Laplace transform gives its expected value [(1+s)^(−1)−∏_i(1+s p_i)^(−1)]/s². The reciprocal substitution t=1/s identifies this scalar integral with the existing determinant-integral definition and supplies integrability. Product integrability and Fubini then identify the Gaussian expected gap. This argument permits zero weights and needs neither entropy moments as an assumption nor an exchange of separately divergent integrals. The theorem concerns diagonal matrices; the common-coordinate matrix representation and pinching inequalities require additional unitary transport.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/GaussianEntropy.diagonal_subentropy_gaussian_gap`
- Dependency: [D5/S3/Quantum/Subentropy/DensityKernel](DensityKernel.md)
- Dependency: [D5/S3/Quantum/Subentropy/GaussianRepresentation](GaussianRepresentation.md)
- Dependency: [D5/S3/Quantum/Subentropy/LaplaceEntropy](LaplaceEntropy.md)

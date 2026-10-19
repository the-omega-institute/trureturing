# The matrix Gaussian entropy expectation

## Abstract

Subentropy is an entropy expectation on the standard Gaussian measure of a common Euclidean space.

Let A be a finite positive semidefinite complex matrix of trace one. Put a_A(z)=Re⟨z,Az⟩/2 and η(u)=−u log u. The standard Gaussian is the real standard Gaussian on the underlying complex Euclidean space. Choose any index i₀ and let κ be the entropy expectation of the corresponding squared pair of independent standard real Gaussian coordinates.

**Theorem 1.1 (A common-coordinate matrix entropy representation).**

$$\operatorname{Integrable}\left(\operatorname{eta}\left(\operatorname{a}\left(A\right)\right), gamma\right) \land \operatorname{Q}\left(A\right) = \operatorname{E}\left(\operatorname{eta}\left(\operatorname{a}\left(A\right)\right)\right) - \operatorname{E}\left(\operatorname{eta}\left(\operatorname{X}\left(i0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/GaussianMatrix.matrix_subentropy_gaussian_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The eigenvalues of A form a probability vector. The existing diagonal entropy representation makes the weighted quadratic entropy integrable. Pairing independent real coordinates realizes the standard Gaussian on the complex Euclidean space, and the eigenvector unitary preserves that Gaussian. Spectral transport identifies the diagonal weighted quadratic form with a_A in these coordinates. Consequently η(a_A) is integrable. The existing isometric-embedding invariance identifies the determinant-integral subentropy with the diagonal one, so Q(A)=Eη(a_A)−κ. Zero and repeated eigenvalues are included. The constant κ is fixed within each matrix dimension and cancels in comparisons on that space.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/GaussianMatrix.matrix_subentropy_gaussian_entropy`
- Dependency: [D5/S3/Quantum/Subentropy/DensityKernel](DensityKernel.md)
- Dependency: [D5/S3/Quantum/Subentropy/GaussianDiagonal](GaussianDiagonal.md)
- Dependency: [D5/S3/Quantum/Subentropy/GaussianQuadratic](GaussianQuadratic.md)

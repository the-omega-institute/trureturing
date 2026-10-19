# Gaussian quadratic forms

## Abstract

Hermitian quadratic forms diagonalize in a Gaussian-preserving spectral basis.

**Definition 1.1 (The normalized quadratic readout).**

Lean statement: `D5/S3/Quantum/Subentropy/GaussianQuadratic.gaussianQuadratic`

*Formalization.* `D5/S3/Quantum/Subentropy/GaussianQuadratic.gaussianQuadratic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

The quadratic readout is one half of the real part of the complex inner product of z with Az, on the complex Euclidean space regarded as a real Gaussian space. In a Hermitian eigenbasis it is one half of the sum of eigenvalue times squared complex coordinate norm. The underlying real linear isometry preserves standard Gaussian measure. Neither identity requires distinct eigenvalues or invertibility.

Positive semidefinite matrices give nonnegative readouts. If the complement I-A is also positive semidefinite, the readout is at most one half the squared norm of z. These quadratic and measure identities supply spectral transport only; they do not assert the entropy expectation representation.

**Definition 1.2 (Pairing real Gaussian coordinates).**

Lean statement: `D5/S3/Quantum/Subentropy/GaussianQuadratic.complexGaussianCoordinates`

*Formalization.* `D5/S3/Quantum/Subentropy/GaussianQuadratic.complexGaussianCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

complexGaussianCoordinates pairs each two independent standard real Gaussian coordinates as the real and imaginary parts of one complex coordinate. Its product-Gaussian pushforward is the standard real Gaussian measure on complex Euclidean space. The squared complex coordinate norm is the sum of the squares of its two real coordinates.

**Theorem 1.3 (The real-coordinate Gaussian law).**

Lean statement: `D5/S3/Quantum/Subentropy/GaussianQuadratic.complex_coordinate_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/GaussianQuadratic.complex_coordinate_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

Pairing independent real standard Gaussian coordinates gives standard Gaussian measure on complex Euclidean space. Each squared complex coordinate norm is exactly the sum of the squares of its two real components. The proof uses the real orthonormal basis consisting of the coordinate vectors and their multiples by the imaginary unit.

**Theorem 1.4 (Gaussian-preserving spectral transport).**

Lean statement: `D5/S3/Quantum/Subentropy/GaussianQuadratic.spectral_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/GaussianQuadratic.spectral_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

The inverse eigenbasis coordinate map of a Hermitian matrix preserves standard Gaussian measure. At every coordinate vector w, the quadratic readout after this map is one half of the sum of lambda_i times normSq(w_i). Zero and repeated eigenvalues are included.

**Theorem 1.5 (Positive quadratic readouts).**

Lean statement: `D5/S3/Quantum/Subentropy/GaussianQuadratic.quadratic_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/GaussianQuadratic.quadratic_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

For a positive semidefinite complex matrix A, gaussianQuadratic A z is nonnegative at every Euclidean vector z. This is the positive-semidefinite quadratic-form law with the positive normalization factor one half.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/GaussianQuadratic.complexGaussianCoordinates`
- Truth anchor: `D5/S3/Quantum/Subentropy/GaussianQuadratic.complex_coordinate_transport`
- Truth anchor: `D5/S3/Quantum/Subentropy/GaussianQuadratic.gaussianQuadratic`
- Truth anchor: `D5/S3/Quantum/Subentropy/GaussianQuadratic.quadratic_nonnegative`
- Truth anchor: `D5/S3/Quantum/Subentropy/GaussianQuadratic.spectral_transport`

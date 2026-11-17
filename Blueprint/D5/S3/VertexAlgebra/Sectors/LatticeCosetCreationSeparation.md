# Native creation-factor separation

## Abstract

LatticeCosetCreationSeparation

**Definition 1.1 (externalLattice).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCreationSeparation.externalLattice`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCreationSeparation.externalLattice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native LatticeData with the given external rank and symmetric even-diagonal block C. It is used for its integral-charge creation polynomials, which do not depend on positivity of C.

**Definition 1.2 (longitudinalPolynomial).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCreationSeparation.longitudinalPolynomial`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCreationSeparation.longitudinalPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual ambient oscillator algebra endomorphism obtained by polynomialProjection followed by polynomialInjection. It replaces every external variable by its longitudinal HB component and fixes every old variable.

**Theorem 1.3 (creationExponential_separation).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCreationSeparation.creationExponential_separation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCreationSeparation.creationExponential_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every native original D, arbitrary finite external rank, integral B, symmetric even-diagonal C, arbitrary external integral charge b and original integral charge n, the native ambient creationExponential at (n,b) equals its image under longitudinalPolynomial multiplied by the native external creationExponential at b after substituting the actual transverse oscillators. This is an equality of full power series in the actual ambient polynomial ring. The linear creationSeries decomposes by X(new)=HB X(old)+T. Its native exponential derivative and coefficient uniqueness identify the product. No positivity, ambient nondegeneracy, rational-charge cocycle or field-factorization premise is assumed. Both finite ranks may be zero.

**Theorem 1.4 (transverse_creation_coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCreationSeparation.transverse_creation_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCreationSeparation.transverse_creation_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive definite original D, arbitrary integral B, symmetric even-diagonal C, external integral charges a,b and natural j, scalarTranslation(a) of the j-th native external creationExponential coefficient is exactly correction(a,b,j) times the polynomial variable to power j. The proof applies the existing creationExponential_factorization to the separated full ambient exponential, cancels its longitudinal factor, whose constant coefficient is one, and evaluates the old oscillator variables at zero. It reuses the full rational Schur binomial computation rather than introducing a separate Gaussian formula. The sign is (-1)^j and the induced normalized mode shift is m-j.

Bakalov-Kac, math/0402315v1, section 4.1, supplies the native creation convention. These oscillator identities supply the creation factor and its exact contraction coefficient. LatticeCosetOperatorCorrection combines these with the native all-source inner expansion to identify the exact two-source finite convolution.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCreationSeparation.creationExponential_separation`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCreationSeparation.externalLattice`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCreationSeparation.longitudinalPolynomial`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCreationSeparation.transverse_creation_coefficient`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeCosetProjectedAction](LatticeCosetProjectedAction.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeCosetSeparation](LatticeCosetSeparation.md)

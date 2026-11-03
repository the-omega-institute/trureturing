# Original Gaussian Cubic Kernel

## Abstract

Original Gaussian Cubic Kernel

Original Laurent residues fix the annular scalar using the original half-binomial period. The signed Neumann blocks and uniqueness equations use the unchanged lp 2 carrier, with the negative mixed identity term. The independently defined cubic kernels and finite external source rows retain the original bilinear Gram form.

These sources are an implementation checkpoint. Native verification and independent admission review are separate requirements; no official acceptance or physical realization is asserted. Full four-halfmode geometry, two-source transport, identityK crossing, Monster moonshine, VOA/CFT/anomaly/fusion, complete string theory and AdS/CFT remain unfinished.

**Theorem 1.1 (annular_moment_identity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.annular_moment_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.annular_moment_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the full complex unit disk, sum the actual Laurent first-moment residues and identify their sum with the original half-binomial period and its derivative.

**Theorem 1.2 (scalar_normalization_iff).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.scalar_normalization_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.scalar_normalization_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original annular residue equation fixes the external complex scalar to scalarC; the proof uses nonvanishing of the actual period.

**Theorem 1.3 (annular_normalization_with_primitive).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.annular_normalization_with_primitive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.annular_normalization_with_primitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An arbitrary sequence of Laurent primitives contributes zero residue, so the original normalization equation has the same unique scalar.

**Theorem 1.4 (original_coefficient_equations_iff).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.original_coefficient_equations_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.original_coefficient_equations_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary original lp 2 source vectors e and f, the two all-mode sewing equations are equivalent to the signed self and mixed Neumann block solution. The mixed block retains its negative identity term.

**Theorem 1.5 (original_row_mem).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.original_row_mem`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.original_row_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finitely supported mixture of both original half-mode sources yields an lp 2 row at every modulus of norm less than one, with no internal cutoff.

**Theorem 1.6 (formal_scalar_normalization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.formal_scalar_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.formal_scalar_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The independently defined formal scalar cancels the all-order Laurent moment against the original period series.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.annular_moment_identity`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.annular_normalization_with_primitive`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.formal_scalar_normalization`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.original_coefficient_equations_iff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.original_row_mem`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel.scalar_normalization_iff`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock](GaussianExternalBlock.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity](OriginalGaussianPeriodIdentity.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent](OriginalGaussianWeightedResolvent.md)

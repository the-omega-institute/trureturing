# GaussianCoefficientScaling

## Abstract

GaussianCoefficientScaling

Diagonal congruence scales each ordinary Gaussian coefficient by the product of its coordinate weights. Principal supports extend this identity to arbitrary index types.

**Theorem 1.1 (Exact finite diagonal congruence).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientScaling.finite_diagonal_congruence`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientScaling.finite_diagonal_congruence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitute X_i by w_i X_i in the actual quadratic Q_K=(1/2) sum_ij K_ij X_i X_j. The algebra homomorphism preserves powers and the scalar 1/n!, while each monomial acquires product_i w_i^d_i. Thus the ordinary gaussianCoefficient transforms by precisely that factor. Zero scalars and odd occupations are included.

**Theorem 1.2 (Principal-support scaling).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientScaling.diagonal_congruence`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientScaling.diagonal_congruence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compute the actual InfiniteGaussianFock.coefficient on the finite principal support of the occupation. Injective mapDomain preserves the product of the diagonal weights. This transfers the finite identity to any index type, with no enumeration or analytic premise.

**Theorem 1.3 (Scaling the external occupation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientScaling.external_scaling`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientScaling.external_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take w=t on external modes and w=1 on internal modes. The exact occupation splitting gives c_(D K D)(d,n)=t^degree(d)c_K(d,n). External coefficients remain ordinary; the internal factorial weight is unchanged.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientScaling.diagonal_congruence`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientScaling.external_scaling`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientScaling.finite_diagonal_congruence`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock](InfiniteGaussianFock.md)

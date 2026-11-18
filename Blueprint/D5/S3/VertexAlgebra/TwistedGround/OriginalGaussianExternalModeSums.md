# Signed Frequency Moment Generators

## Abstract

Signed Frequency Moment Generators

**Theorem 1.1 (sourceMoment_generators).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.sourceMoment_generators`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.sourceMoment_generators` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both original U mode series are differentiated A generators on norm(u)+norm(x)<1. The positive sum equals u(1-u) Mplus derivative +(1-3u) Mplus/2 - Aminus(0)/2. Multiplying the negative sum by u gives u(1-u) Mminus derivative -(u+1) Mminus/2 + Aminus(0)/2. The actual input-zero term is retained in both equations.

**Theorem 1.2 (sourceMoment_generators_explicit).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.sourceMoment_generators_explicit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.sourceMoment_generators_explicit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the same joint disk, the positive U sum is Mplus times (1-2u+(1-x)u squared)/(2(1-(1-x)u)) minus Aminus(0)/2. The negative U sum multiplied by u is Mminus times (u(1-u)/(2(1-x-u))-1/2) plus Aminus(0)/2. The mode derivative follows from normal convergence and the actual algebraic generator square.

**Theorem 1.3 (mode_derivative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.mode_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.mode_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either sign on norm(u)+norm(x)<1, the differentiated actual sourceAmplitude mode series has sum equal to the first external-variable derivative of sourceMode, and sourceMode is complex differentiable there.

**Theorem 1.4 (mode_factors_ne_zero).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.mode_factors_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.mode_factors_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the same joint disk the factors 1-u, 1-(1-x)u and 1-x-u are all nonzero.

**Theorem 1.5 (mode_derivative_explicit).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.mode_derivative_explicit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.mode_derivative_explicit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either sign on the same disk, with a=1 and b=1-x for the positive sign and a=1-x and b=1 for the negative sign, the external-variable derivative of the actual sourceMode equals sourceMode times [1/(2(1-u))+b/(2(a-bu))].

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.mode_derivative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.mode_derivative_explicit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.mode_factors_ne_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.sourceMoment_generators`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.sourceMoment_generators_explicit`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators](OriginalGaussianExternalGenerators.md)

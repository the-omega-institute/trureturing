# Signed Generated Source Displacement

## Abstract

Signed Generated Source Displacement

**Theorem 1.1 (boundary_normalization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.boundary_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.boundary_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real 0<r<1, sqrt(1-r) times the actual sourceAmplitude(false,0,r) equals one. The actual analytic binomial branch supplies this normalization.

**Definition 1.2 (modeScale).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.modeScale`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.modeScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For either signed label and complex u, modeScale is 1 for the positive label and u for the negative label. This polynomial multiplier preserves the negative zero-mode boundary without dividing by u.

**Definition 1.3 (modeA).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.modeA`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.modeA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For either label and complex u,x, modeA is the scaled actual U amplitude: positive (1-2u+(1-x)u squared)/(2(1-(1-x)u)), negative u(1-u)/(2(1-x-u))-1/2.

**Definition 1.4 (modeB).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.modeB`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.modeB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For either label modeB is the scaled boundary coefficient, positive 1/2 and negative -1/2.

**Definition 1.5 (modeH).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.modeH`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.modeH` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For either label and complex u,x,lambdaRatio, modeH is the scaled diagonal jet amplitude: positive -xu/(1-(1-x)u), negative xu/(1-x-u), in either case minus modeA and minus 2x modeScale lambdaRatio.

**Theorem 1.6 (external_displacement_generated).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.external_displacement_generated`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.external_displacement_generated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all signed labels, 0<r<1 and norm(u)+r,norm(v)+r<1, the complete double mode series of the original J frequency sum and original T frequency difference converge to (1-r)(UV+VU)/2 and (1-r)(UV-VU)/2, respectively. Every summand carries both modeScale multipliers and u to p times v to q. Here U=M modeA-modeB Aminus(0), V=M modeH+modeB Aminus(0), x=r and lambdaRatio is the original period logarithmic derivative. These are genuine normally convergent source displacement sums; identification of the left sums with differential operators on J/T remains separate.

**Theorem 1.7 (external_negative_zero_generated).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.external_negative_zero_generated`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.external_negative_zero_generated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either remaining label, 0<r<1 and norm(u)+r<1, the complete original negative-zero J row with modeScale weight sums to sqrt(1-r)/2 times M(modeH-modeA) plus modeB. The actual binomial branch proves sqrt(1-r) Aminus(0)=1. The original negative-zero T row sums to sqrt(1-r)/2 times M(modeH+modeA). The T identity contribution is included.

**Theorem 1.8 (external_radial_generated).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.external_radial_generated`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.external_radial_generated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all signed labels, 0<r<1 and norm(u)+r,norm(v)+r<1, the complete scaled two-mode T radial remainder sums to (1-r)(VV-UU)/2. The summand is 2r times the actual fixed-mode radial derivative minus both frequency actions, with both modeScale factors and u/v powers. U,V are the same literal source amplitudes as in the displacement sums. This does not yet exchange the radial derivative with the complete two-mode T sum.

**Definition 1.9 (kernelMode).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.kernelMode`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.kernelMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For three Boolean labels and complex u,v,z, this is the literal full two-mode tsum of externalT when square is true and externalJ otherwise, with u to p times v to q. It assumes no candidate kernel value.

**Theorem 1.10 (kernelMode_derivative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.kernelMode_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.kernelMode_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either original J or T and all signed modes, norm(u)+norm(z)<1 and norm(v)+norm(z)<1 justify the complex derivative in u. The series of p times the original kernel coefficient times u to p-minus-one times v to q has that derivative as its sum. Normal convergence is proved on an intermediate mode disk from the actual bilinear contraction bound.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.boundary_normalization`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.external_displacement_generated`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.external_negative_zero_generated`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.external_radial_generated`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.kernelMode`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.kernelMode_derivative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.modeA`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.modeB`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.modeH`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.modeScale`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalJetSums](OriginalGaussianExternalJetSums.md)

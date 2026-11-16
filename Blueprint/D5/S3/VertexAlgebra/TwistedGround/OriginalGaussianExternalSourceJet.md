# Diagonal Source Derivative and the Actual Jet

## Abstract

Diagonal Source Derivative and the Actual Jet

The actual source_pairings_explicit and scaled radial column derivative first differentiate sourceExternal. Multiplication by the original period then differentiates A. This fixes the diagonal jet and feeds the actual displacement and radial equations; it does not assume kernel identification.

**Theorem 1.1 (hasDerivAt_radial_sourceExternal).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet.hasDerivAt_radial_sourceExternal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet.hasDerivAt_radial_sourceExternal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every signed mode and 0<r<1, sourceExternal at sqrt(r) has real derivative -(U+V)/(2r F).

**Theorem 1.2 (hasDerivAt_radial_sourceAmplitude).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet.hasDerivAt_radial_sourceAmplitude`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet.hasDerivAt_radial_sourceAmplitude` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every signed mode and 0<r<1, the real derivative of A(r) is Fprime*A/F+(U+V)/(2r); Fprime is shiftedCentralDerivative at shift zero.

**Theorem 1.3 (sourceJetMoment_eq_derivative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet.sourceJetMoment_eq_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet.sourceJetMoment_eq_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every signed mode and 0<r<1, V equals 2r times the total real derivative of A minus the mode frequency U minus 2r A Fprime/F.

**Theorem 1.4 (external_source_equations).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet.external_source_equations`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet.external_source_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of signed natural modes and 0<r<1, all three genuine equations hold together: the J frequency sum, the T frequency difference, and the real T radial derivative. Their right sides use U=modeFrequency A and V=2r A derivative-U-2r A Fprime/F, with coefficients (1-r)/2 and the radial divisor 2r retained.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet.external_source_equations`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet.hasDerivAt_radial_sourceAmplitude`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet.hasDerivAt_radial_sourceExternal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet.sourceJetMoment_eq_derivative`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution](OriginalGaussianExternalEvolution.md)

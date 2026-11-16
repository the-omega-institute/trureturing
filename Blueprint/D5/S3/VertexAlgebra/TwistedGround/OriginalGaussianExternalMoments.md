# Explicit Source Moments in Displacement

## Abstract

Explicit Source Moments in Displacement

U and V are the convergent original shifted-central and centralColumnJet pairings. The public radial inverse-column formulas fix their signs and the square-root factor; these are actual source contractions.

**Definition 1.1 (sourceMoment).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.sourceMoment`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.sourceMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

U is the shifted sum over n>=0 of (n+1)(-1)^(n+1) choose(alpha,n+1) x^(n+1) C_(n+1).

**Definition 1.2 (sourceJetMoment).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.sourceJetMoment`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.sourceJetMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

V is the shifted sum over n>=0 of (-1)^(n+1) choose(alpha,n+1) x^(n+1) H_(n+1), with the original centralColumnJet H.

**Theorem 1.3 (sourceMoment_eq_modeFrequency).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.sourceMoment_eq_modeFrequency`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.sourceMoment_eq_modeFrequency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every signed mode and norm(x)<1, U equals the signed mode frequency of A. The constant internal frequency cancels.

**Theorem 1.4 (source_moment_pairings).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.source_moment_pairings`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.source_moment_pairings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every signed mode and real 0<r<1, pairing its actual external vector with Rminus w gives -sqrt(1-r) U, and pairing with Rplus w gives -sqrt(1-r) V.

**Theorem 1.5 (external_displacement_explicit).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.external_displacement_explicit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.external_displacement_explicit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all signed modes and 0<r<1, the actual J frequency sum equals (1-r)(U_p V_q+V_p U_q)/2, while the actual T frequency difference equals (1-r)(U_p V_q-V_p U_q)/2.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.external_displacement_explicit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.sourceJetMoment`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.sourceMoment`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.sourceMoment_eq_modeFrequency`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.source_moment_pairings`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalDisplacement](OriginalGaussianExternalDisplacement.md)

# The Literal Hyperbolic Certificate

## Abstract

The literal frame has twenty-four singular vectors and all hyperbolic polar pairings.

**Theorem 1.1 (The Literal Hyperbolic Certificate).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/LeechHyperbolicCertificate.literal_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/LeechHyperbolicCertificate.literal_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal binary integer vectors reduce to the original lattice mod-two charge space. Each of the twenty-four half Gram norms reduces to zero; the 576 Gram pairings reduce to one exactly on partner pairs and zero otherwise.

The original quadratic reduction identity transports the integer norm checks to the original cocycle diagonal. The original Gram reduction transports the polar checks to modTwoPairing. Evaluating a dependence against partner vectors then yields the hyperbolic basis used by the native representation construction.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/LeechHyperbolicCertificate.literal_certificate`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/LeechFrameRows](LeechFrameRows.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/LeechQuadraticReduction](LeechQuadraticReduction.md)

# Applications of the literal kernel identity

## Abstract

Complex radial identities for all signs of the original J and T kernels

In each identity u, v and z are complex and satisfy ‖u‖ + ‖z‖ < 1 and ‖v‖ + ‖z‖ < 1. The sign labels e and f are Booleans, with true denoting the positive label. The candidates on the right are the signed formulas of OriginalGaussianExternalSignedCandidate.

**Theorem 1.1 (Positive J equality).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.positiveJ_eq_candidateJ_complex`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.positiveJ_eq_candidateJ_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On this domain, kernelMode(false,true,true,u,v,z) = candidateJ(true,true,u,v,z²). The two-positive signed formula is the positive J formula. `D5/S3/VertexAlgebra/TwistedGround/PositiveJ/Identification.positiveJ_eq_candidateJ` supplies the real equality for kernelMode_eq_candidate_complex_of_real.

**Theorem 1.2 (J equality with a negative label).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.signedJ_eq_candidateJ_complex`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.signedJ_eq_candidateJ_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On this domain, if e = false or f = false, kernelMode(false,e,f,u,v,z) = candidateJ(e,f,u,v,z²). The transport theorem takes its real equality from OriginalGaussianSignedIdentification.six_sector_identification with square = false.

**Theorem 1.3 (J equality for every sign pair).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsJ_eq_candidateJ_complex`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsJ_eq_candidateJ_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary e and f on this domain, kernelMode(false,e,f,u,v,z) = candidateJ(e,f,u,v,z²). The three pairs with a false label use signedJ_eq_candidateJ_complex. The pair (true,true) uses positiveJ_eq_candidateJ_complex.

**Theorem 1.4 (T equality with a negative label).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.signedT_eq_candidateT_complex`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.signedT_eq_candidateT_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On this domain, if e = false or f = false, kernelMode(true,e,f,u,v,z) = candidateT(e,f,u,v,z²). The transport theorem takes its real equality from OriginalGaussianSignedIdentification.six_sector_identification with square = true.

**Theorem 1.5 (Positive T equality).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.positiveT_eq_candidateT_complex`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.positiveT_eq_candidateT_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On this domain, kernelMode(true,true,true,u,v,z) = candidateT(true,true,u,v,z²). The two-positive signed T formula agrees with the positive rational candidate by the equality of their denominators and numerators. PositiveT.GeneratorIdentification.positiveT_eq_candidateT then supplies the real equality for kernelMode_eq_candidate_complex_of_real.

**Theorem 1.6 (T equality for every sign pair).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsT_eq_candidateT_complex`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsT_eq_candidateT_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary e and f on this domain, kernelMode(true,e,f,u,v,z) = candidateT(e,f,u,v,z²). The three pairs with a false label use signedT_eq_candidateT_complex. The pair (true,true) uses positiveT_eq_candidateT_complex.

**Theorem 1.7 (Joint J and T identities).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsJT_eq_candidates_complex`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsJT_eq_candidates_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same arbitrary pair e and f on this domain, kernelMode(false,e,f,u,v,z) = candidateJ(e,f,u,v,z²) and kernelMode(true,e,f,u,v,z) = candidateT(e,f,u,v,z²). The conjunction uses allSignsJ_eq_candidateJ_complex and allSignsT_eq_candidateT_complex directly.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsJT_eq_candidates_complex`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsJ_eq_candidateJ_complex`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsT_eq_candidateT_complex`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.positiveJ_eq_candidateJ_complex`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.positiveT_eq_candidateT_complex`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.signedJ_eq_candidateJ_complex`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.signedT_eq_candidateT_complex`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/PositiveJ/Identification.positiveJ_eq_candidateJ`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Transport](Transport.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/PositiveJ/Identification](../PositiveJ/Identification.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification](../PositiveT/GeneratorIdentification.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Signed/Identification](../Signed/Identification.md)

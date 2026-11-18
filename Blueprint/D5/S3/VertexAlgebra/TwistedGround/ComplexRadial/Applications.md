# All Signed Original Gaussian Kernels at Complex Radius

## Abstract

All Signed Original Gaussian Kernels at Complex Radius

For all four Boolean sign pairs and both J and T, the original all-mode kernels at arbitrary complex z equal the literal signed candidates at z^2 whenever norm(u)+norm(z)<1 and norm(v)+norm(z)<1. The positive cases consume the existing positive J and positive T generating-kernel identifications; the other sectors consume the actual signed identifications. Axes, diagonal and z=0 are included. This is an integration of those existing real results with complex holomorphy and identity transport. Full finite-mode coefficient extraction and the wider Monster/VOA/string-theory objective remain open.

**Theorem 1.1 (positiveJ_eq_candidateJ_complex).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.positiveJ_eq_candidateJ_complex`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.positiveJ_eq_candidateJ_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive J kernel equals the signed positive J formula on the original complex source domain.

**Theorem 1.2 (signedJ_eq_candidateJ_complex).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.signedJ_eq_candidateJ_complex`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.signedJ_eq_candidateJ_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every J sector with a negative label equals its signed candidate on the original complex source domain.

**Theorem 1.3 (allSignsJ_eq_candidateJ_complex).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsJ_eq_candidateJ_complex`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsJ_eq_candidateJ_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All four J sign sectors satisfy the exact complex radial identification.

**Theorem 1.4 (signedT_eq_candidateT_complex).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.signedT_eq_candidateT_complex`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.signedT_eq_candidateT_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every T sector with a negative label equals its signed candidate on the original complex source domain.

**Theorem 1.5 (positiveT_eq_candidateT_complex).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.positiveT_eq_candidateT_complex`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.positiveT_eq_candidateT_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive T kernel equals the signed positive T formula, consuming the actual positive T generator theorem and the exact candidate denominator identification.

**Theorem 1.6 (allSignsT_eq_candidateT_complex).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsT_eq_candidateT_complex`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsT_eq_candidateT_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All four T sign sectors satisfy the exact complex radial identification.

**Theorem 1.7 (allSignsJT_eq_candidates_complex).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsJT_eq_candidates_complex`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsJT_eq_candidates_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all e,f:Bool and u,v,z:Complex, the only hypotheses are norm(u)+norm(z)<1 and norm(v)+norm(z)<1. Both literal original kernelMode(false,e,f,u,v,z)=candidateJ(e,f,u,v,z^2) and kernelMode(true,e,f,u,v,z)=candidateT(e,f,u,v,z^2) hold. No regularity, equality, nonzero or PDE premise is added.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsJT_eq_candidates_complex`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsJ_eq_candidateJ_complex`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.allSignsT_eq_candidateT_complex`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.positiveJ_eq_candidateJ_complex`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.positiveT_eq_candidateT_complex`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.signedJ_eq_candidateJ_complex`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications.signedT_eq_candidateT_complex`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Transport](Transport.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification](../PositiveT/GeneratorIdentification.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Signed/Identification](../Signed/Identification.md)

# Original Signed Gaussian Identification

## Abstract

Original Signed Gaussian Identification

Let r be real with 0<r<1 and let norm(u)+sqrt(r)<1 and norm(v)+sqrt(r)<1. In each sector with at least one negative label, the original J and T generators equal their explicit signed analytic candidates. The proof subtracts the exact spatial equations, including the J constant, obtains genuine joint differentiability from the original bilinear resolvent and candidate analyticity, and applies spatial uniqueness on radius 1-sqrt(r). This result concerns real radial r; extension to arbitrary complex source parameters requires analytic continuation.

**Theorem 1.1 (signedJ_eq_candidateJ).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/Identification.signedJ_eq_candidateJ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/Identification.signedJ_eq_candidateJ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either pair e,f of Boolean labels with e=false or f=false, the original kernelMode(false,e,f,u,v,sqrt(r)) equals candidateJ(e,f,u,v,r), for every real 0<r<1 and complex u,v satisfying the original source bidisk bounds. There are no additional source, regularity, equality, boundary or nonzero-denominator assumptions.

**Theorem 1.2 (signedT_eq_candidateT).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/Identification.signedT_eq_candidateT`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/Identification.signedT_eq_candidateT` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either pair e,f of Boolean labels with e=false or f=false, the original kernelMode(true,e,f,u,v,sqrt(r)) equals candidateT(e,f,u,v,r), for every real 0<r<1 and complex u,v satisfying the original source bidisk bounds. The conclusion includes both axes, the origin and the diagonal.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/Identification.signedJ_eq_candidateJ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/Identification.signedT_eq_candidateT`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial](JSpatial.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Signed/SpatialUniqueness](SpatialUniqueness.md)

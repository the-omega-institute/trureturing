# Inverse local coordinates and source transport

## Abstract

Signed sources in physical four-point coordinates

**Definition 1.1 (Native flags of each physical puncture).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.flags`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.flags` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first flag is true on the right leg and the second is true for the positive mode sign. In puncture order P, Q, R, S, chart A has flags (false,false), (false,true), (true,false), (true,true). Chart B has (true,false), (false,false), (false,true), (true,true). Chart D has (false,false), (true,false), (false,true), (true,true).

**Definition 1.2 (Inverse physical displacement).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.rawLocal`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.rawLocal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For physical displacement u at a puncture, use the chart scale s and lowering parameter λ to recover the native displacement v = u/(s + λu).

**Definition 1.3 (Chosen half-Jacobian).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.halfJacobian`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.halfJacobian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a native displacement v and its inverse root β satisfying β² = 1−λv, the chosen half-Jacobian is scaleRoot(c,x,p)/β³.

**Definition 1.4 (Normalized root in the inverse coordinate).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.inverseRoot`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.inverseRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any chart c, real x, puncture p and complex u, write s = scale(c,x,p), λ = loweringParameter(c,p) and v = u/(s + λu). The inverse root is (1 − λv)^(1/2), taken by complex principal power and normalized to 1 at u = 0.

**Definition 1.5 (Signed source in the physical coordinate).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.physicalSource`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.physicalSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any chart c, real x, puncture p and complex u, use the flags (l,e) of p and the inverse coordinate v and root β just defined. The source is legSign(l) · chosenChartSource(c,x,e,v) / (scaleRoot(c,x,p)/β³). The leg sign is −1 on the right and +1 on the left. Put r = parameter(c,x), and let R be 1 for the positive mode and periodRoot(c,x) for the negative mode. The chosen source is t^(−1/2)/(b(v)R) with principal complex power, where t is h(e,v,r)/b(v) in the positive mode and h(e,v,r)/(b(v)(1 − r)) in the negative mode.

**Theorem 1.6 (Analyticity in the physical coordinate).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.physicalSource_analytic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.physicalSource_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real 0 < x < 1, the physical source of each chart and puncture is analytic at displacement u = 0. The chosen half-Jacobian is nonzero there.

**Theorem 1.7 (Source germs on the B and D overlaps).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.signed_physical_source_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.signed_physical_source_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix real 0 < x < 1 and any puncture p. Write M_c(u) for physicalSource in chart c. On a neighborhood of u = 0, both (−i√x)⁻¹ M_A(u) = relativeB(p) M_B(u) and i⁻¹ M_A(u) = relativeD(p) M_D(u) hold, with √x the positive real root. The B sign is −1 at S and +1 elsewhere. The D sign is −1 at Q and R and +1 elsewhere. The squared sources become the same reciprocal physical polynomial after the lift factors are included. Their signed sums are nonzero at the origin by the center normalization and remain nonzero on a neighborhood, so equality of squares gives equality of the signed sources there.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.flags`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.halfJacobian`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.inverseRoot`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.physicalSource`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.physicalSource_analytic`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.rawLocal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.signed_physical_source_transport`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct](OriginalFourMChartProduct.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap](OriginalFourMSignedOverlap.md)

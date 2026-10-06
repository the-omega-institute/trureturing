# One shared body from the actual length Gram matrix

## Abstract

The common six-length cut body has a Lorentz and upper-half-space coordinate realization.

Let l be six positive real lengths in the order (01,02,03,23,13,12). The symmetric matrix G has diagonal entries one and off-diagonal entries minus cosh of the corresponding length. The set C consists of nonnegative four-coordinate vectors whose coordinates sum to one and whose four G-row values are nonpositive. Write q(v)=v-transpose G v, r(v)=v/sqrt(-q(v)), and b=(1/4,1/4,1/4,1/4). R6 and R4 denote real coordinate spaces. B is the Lorentz form with signs (+,+,+,-). The function phi01 is the original six-variable cosine formula applied to cosh(l). For a future unit timelike y, Psi(y) has horizontal coordinate (y0+i*y1)/(y3-y2) and height 1/(y3-y2). H3 denotes the repository's HyperbolicThreeSpace with its actual metric topology.

**Theorem 1.1 (Compactness, explicit frame and shared coordinate map).**

$$\forall l \in R6,\; \left(\forall k \in Fin\left(6\right),\; 0 < l\left(k\right)\right) \Rightarrow \left(IsCompact\left(C\left(l\right)\right) \land \left(b \in C\left(l\right) \land \left(\left(\forall i \in Fin\left(4\right),\; Gb\left(l, i\right) < 0\right) \land \left(\left(\forall v \in R4,\; v \in C\left(l\right) \Rightarrow q\left(l, v\right) < 0\right) \land \left(ContinuousOn\left(r\left(l\right), C\left(l\right)\right) \land \left(InjOn\left(r\left(l\right), C\left(l\right)\right) \land \left(IsCompact\left(image\left(r\left(l\right), C\left(l\right)\right)\right) \land \left(Nonempty\left(image\left(r\left(l\right), C\left(l\right)\right)\right) \land \left(\left(\forall v \in R4,\; v \in C\left(l\right) \Rightarrow q\left(l, r\left(l, v\right)\right) = -1\right) \land \left(\left(-1 < phi01\left(l\right) \land phi01\left(l\right) < 1\right) \Rightarrow \left(\exists m \in Matrix4,\; \left(\forall i \in Fin\left(4\right),\; \forall j \in Fin\left(4\right),\; B\left(row\left(m, i\right), row\left(m, j\right)\right) = G\left(l, i, j\right)\right) \land \left(0 < det\left(m\right) \land \left(det\left(G\left(l\right)\right) < 0 \land \left(\exists f \in Maps\left(C\left(l\right), H3\right),\; Continuous\left(f\right) \land \left(Injective\left(f\right) \land \left(IsCompact\left(range\left(f\right)\right) \land \left(Nonempty\left(range\left(f\right)\right) \land \left(\forall v \in C\left(l\right),\; \exists y \in R4,\; y = vecMul\left(r\left(l, v\right), m\right) \land \left(B\left(y, y\right) = -1 \land \left(0 < coord\left(y, 3\right) \land coordinates\left(f\left(v\right)\right) = Psi\left(y\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LengthGramBody.shared_radial_body` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The barycenter strictly satisfies every cut. A cut equality at a positive coordinate forces that coordinate to exceed one half. If q vanished, every positive coordinate would require a cut equality. Two positive coordinates cannot both exceed one half, while a singleton support violates its own cut. Thus q is strictly negative throughout the same C.

The positive square-root denominator makes r continuous. The sum of the image coordinates recovers its reciprocal scale, so r is injective. Its image is compact and nonempty, and the quadratic value there equals minus one.

The strict condition on phi01 makes the final square root in the explicit four-vector frame positive. The frame's Lorentz Gram is exactly G and its determinant is positive. Congruence with diag(1,1,1,-1) gives det(G)<0. Every point of the same radial body is future unit timelike. Its positive denominator y3-y2 defines Psi throughout C. The coordinate inverse proves injectivity, and the existing coordinate homeomorphism proves continuity into actual H3.

This closes the shared compact coordinate-body and frame step of the original six-length construction. It does not yet assert three-dimensional interior, complete triangular/hexagonal incidence, geodesic intervals, prescribed edge distances, dihedral angles or relabeling isometries. Those obligations retain the original all-six strict source cosine domain; one strict condition suffices for this frame step.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LengthGramBody.shared_radial_body`
- Dependency: [D5/S3/Geometry/HyperbolicTopology](../HyperbolicTopology.md)
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleEnvelopes](FourCycleEnvelopes.md)

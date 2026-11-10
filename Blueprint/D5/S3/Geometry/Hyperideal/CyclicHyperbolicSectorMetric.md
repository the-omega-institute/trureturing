# Original chains in cyclic hyperbolic sectors

## Abstract

Original finite chains attain the capped angular metric in numbered hyperbolic sectors.

Let H3 denote HyperbolicThreeSpace with its original metric and let Phi be LengthGramMetricSegments.lift, with Lorentz coordinates (x,y,u,v) of signature (1,1,1,-1). For 0<alpha<pi, S(alpha) is the actual closed subset defined by y>=0 and cos(alpha)*y-sin(alpha)*x<=0. It inherits the original H3 distance and includes the axis x=y=0. The upper face is the equality cos(alpha)*y-sin(alpha)*x=0 within S(alpha); the lower face is y=0 within S(alpha). These are complete faces, including the axis.

Choose any natural number n and widths alpha(i) in (0,pi), indexed by Fin(n+1). Set b(i)=sum over k<i of alpha(k), and A=sum over all k of alpha(k). The datum G(alpha) is cyclicDatum: its numbered source piece i is S(alpha(i)), its generator i goes to the next cyclic index, and its actual partial isometry rotates the complete upper face by -alpha(i) to the next complete lower face. All rotations preserve the actual axis. The source is the disjoint union of these actual subsets; equal underlying H3 coordinates in different source tags are distinct representatives. The relation, paid moves, forward and backward zero-cost seam moves, and distance infimum are exactly those of FiniteOrbitChainMetric.Datum.

For a point p with Phi(p)=(x,y,u,v), set r(p)=arsinh(norm(x+iy)), z(p)=arsinh(u/cosh(r(p))), and t(p)=arg(x+iy). Within S(alpha), t(p) lies in [0,alpha]. On the axis it is zero. Write C(r,z,t) for the actual H3 point whose lift is (sinh(r)*cos(t),sinh(r)*sin(t),cosh(r)*sinh(z),cosh(r)*cosh(z)). Then p=C(r(p),z(p),t(p)); at r=0 the point C is independent of its last argument.

For tagged p=(i,p0), put Theta(p)=b(i)+t(p0). For tagged p,q define dbar(p,q)=min(pi,norm([Theta(q)-Theta(p)] in AddCircle(A))), and L(alpha,p,q)=dist_H3(C(r(p0),z(p0),0),C(r(q0),z(q0),dbar(p,q))). This is comparisonLength. The scalar angular circle retains the period A even when A exceeds 2pi. No new three-dimensional quotient or distance is introduced.

**Theorem 1.1 (The original chain metric and an attaining finite chain).**

$$\forall n \in Nat,\; \forall alpha \in Maps\left(Fin\left(n+1\right), Real\right),\; \left(\forall i \in Fin\left(n+1\right),\; 0 < alpha\left(i\right) \land alpha\left(i\right) < pi\right) \Rightarrow \left(\forall p \in Source\left(alpha\right),\; \forall q \in Source\left(alpha\right),\; Chain\left(G\left(alpha\right), p, q, ofReal\left(L\left(alpha, p, q\right)\right)\right) \land delta\left(G\left(alpha\right), p, q\right) = ofReal\left(L\left(alpha, p, q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/CyclicHyperbolicSectorMetric.cyclic_sector_metric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every choice of the widths and every pair of original tagged representatives, an original finite Chain from p to q has cost ofReal(L(alpha,p,q)), and the literal original cost infimum delta(G(alpha),p,q) equals that cost. Every competing chain, including repeated seams, inverse transitions, winding and axis visits, has at least this cost. No restriction on total angle A or radial and axial coordinates is imposed.

Fix the first endpoint p and define h(theta)=min(pi,norm([theta-Theta(p)] in AddCircle(A))). Map each point x in source piece i to C(r(x),z(x),h(b(i)+t(x))). The reverse triangle inequality for the scalar circle norm, followed by the real truncation, gives abs(h(s)-h(t))<=abs(s-t). Two angles in the same actual source sector differ by less than pi. The exact cylindrical distance identity is cosh(dist(C(r,z,s),C(R,Z,t)))=cosh(r)*cosh(R)*cosh(z-Z)-sinh(r)*sinh(R)*cos(s-t). Monotonicity of cosine on [0,pi] and of hyperbolic cosine on nonnegative distances shows that this map does not increase distances within any source piece.

A non-axis upper-face point has local angle alpha(i), and its rotated lower-face representative has local angle zero. The cumulative angles agree in AddCircle(A) across every designated seam, including the closing seam. The radial and axial coordinates are preserved by the actual rotations. At axis points the cylindrical image ignores the angle. Thus the maps on all numbered pieces agree on every original forward or inverse identification.

Induction on the original Chain constructors bounds the image distance by the accumulated cost: a paid move uses the source nonexpansion and triangle inequality, while either seam move leaves the image fixed. Taking the original infimum gives the displayed bound. Because the fold depends on p, the argument does not assert that a single fixed H3 map realizes all pairwise capped angular distances.

For the upper comparison, choose the shorter of the two cyclic forward runs between the original tags and local endpoint angles. A run may traverse a complete cycle when the tags coincide. Apart from the identical angle representative, the two nonnegative spans sum to A; their minimum equals the scalar angular norm. When this minimum is below pi, recursively cross the successive upper faces on the developed hyperbolic segment. Its lift is a positive sinh interpolation of the endpoints. A common open transverse half-plane orients every wall crossing onto the positive wall ray and excludes the axis. Rotate the crossing by the actual seam map and continue in the next sector. The exact between-distance splits add to the original developed distance. Closed-wall endpoints use the endpoint itself, retaining its radial and axial coordinates.

When the scalar angular norm is at least pi, use the hyperbolic segment between opposite transverse rays. A transverse sign change gives a common axis point on this segment, even for unequal axial coordinates. Rotate its two halves onto the actual endpoint rays and join their original tags by a zero-cost finite seam walk at the axis. An endpoint on the axis uses that endpoint as the common point. These constructions attain L in every branch. Identifying this sector model with an original CFMP edge star still requires simultaneous axis coordinates, original face transports, the dihedral-angle and orbit correspondences, and a confinement radius for competing chains.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/CyclicHyperbolicSectorMetric.cyclic_sector_metric`
- Dependency: [D5/S3/Geometry/HyperbolicSupportBoundary](../HyperbolicSupportBoundary.md)
- Dependency: [D5/S3/Geometry/Hyperideal/CyclicHyperbolicSectorSupport](CyclicHyperbolicSectorSupport.md)
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramMetricSegments](LengthGramMetricSegments.md)
- Dependency: [D5/S3/Topology/FiniteOrbitChainMetric](../../Topology/FiniteOrbitChainMetric.md)

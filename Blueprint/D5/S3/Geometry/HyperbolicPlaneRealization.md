# Spacelike supporting planes in the original hyperbolic metric

## Abstract

Full actual-metric realization of original Lorentz supporting planes.

Write B(X,Y)=X0*Y0+X1*Y1+X2*Y2-X3*Y3 on R4. H2 is Mathlib UpperHalfPlane with its hyperbolic distance and H3 is HyperbolicThreeSpace with the repository's existing hyperbolic distance. For p with horizontal coordinate x+i*y and height h>0, Phi(p) is the original LengthGramMetricSegments.lift: (x/h,y/h,(x*x+y*y+h*h-1)/(2*h),(x*x+y*y+h*h+1)/(2*h)). Pi(N) denotes exactly {p in H3 : B(Phi(p),N)=0}. Maps denotes functions, Range their complete image, and Isometry refers to these actual metrics.

**Theorem 1.1 (Every spacelike supporting plane is an entire isometric hyperbolic plane).**

$$\forall N \in R4,\; 0 < B\left(N, N\right) \Rightarrow \left(\exists e \in Maps\left(H2, H3\right),\; Isometry\left(e\right) \land Range\left(e\right) = Pi\left(N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/HyperbolicPlaneRealization.supporting_plane_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James W. Cannon, William J. Floyd, Richard Kenyon, and Walter R. Parry (1997). *Hyperbolic Geometry*. URL: <https://library.slmath.org/books/Book31/files/cannon.pdf>.

*Commentary.*

For B(N,N)>0 put r=sqrt(B(N,N)), and choose s=r when N1>=0 and s=-r otherwise. With E1=(0,1,0,0) put M=N+s*E1. Then s is nonzero, s*s=B(N,N), s*N1>=0, and d=B(M,M)=2*(B(N,N)+s*N1)>0. The auxiliary Lorentz reflection R(X)=X-2*B(X,M)/d*M preserves B, satisfies R(R(X))=X, and B(R(X),N)=-s*X1. Involution directly applies the pinned Mathlib Module.involutive_preReflection to the real linear functional f(X)=2*B(X,M)/d, with f(M)=2; preReflection M f is exactly R. Linearity uses the original lorentz_linear theorem. This construction covers both N2=N3 and N2!=N3; it never divides by N2-N3.

The reflection preserves the future unit sheet. Indeed B(X,R(X))=-1-2*B(X,M)^2/d<0 for B(X,X)=-1. If X3>0 and a unit timelike Y had Y3<=0, finite-dimensional Cauchy-Schwarz would contradict B(X,Y)<0. Apply this to Y=R(X). Thus the original projection Psi(Y)=((Y0+i*Y1)/(Y3-Y2),1/(Y3-Y2)) is defined: future_den supplies Y3-Y2>0. The original lift_of_coordinates supplies Phi(Psi(Y))=Y.

Embed z=u+i*v from H2 vertically as vmap(z)=(u,0,v) in H3 and define e(z)=Psi(R(Phi(vmap(z)))). The existing H2 cosh_dist' formula gives B(Phi(vmap(z)),Phi(vmap(w)))=-cosh(dist_H2(z,w)); the original lift_cosh gives the corresponding H3 equation. Reflection preserves their pairing, and strict monotonicity of cosh on nonnegative distances proves Isometry(e).

For surjectivity, take any p with B(Phi(p),N)=0. Y=R(Phi(p)) is future unit, and the reflection identity plus its involution imply Y1=0 because s!=0. Set z=Y0/(Y3-Y2)+i/(Y3-Y2). Its imaginary part is strictly positive. The original inverse-coordinate theorem gives Phi(vmap(z))=Y; involution and lift_injective then give e(z)=p. Conversely every e(z) is orthogonal to N because Phi(vmap(z))1=0. Thus the range equality includes every point of the original plane, without a surjectivity or isometry assumption.

The source attribution concerns classical hyperbolic model transport and Lorentz geometry: Cannon-Floyd-Kenyon-Parry (1997), Theorem 9.3 and page 80, then Section 10, Theorem 10.1 on page 82 (including upper-sheet preservation) and the distance lemma on page 83. The exact realization in these existing repository types is a repository derivation. No mathematical novelty is claimed.

For the later original CFMP sections 65-66 application, retain one and the same supplied Gram frame m, radial map and map f from cutBody(l). The six positive lengths remain in order (01,02,03,23,13,12), with all six strict source cosine inequalities retained in that application. For each already identified spacelike normal N in this original frame, this theorem identifies its exact zero locus as an actual hyperbolic plane. The reflection is an auxiliary parametrization; it does not replace m, f or their body. The corresponding halfspace intersection equality uses the existing normal correspondence and coefficient normalization, not a new tetrahedron. This generic theorem assumes no tetrahedron or cosine data and does not itself verify those normal correspondences.

Actual dihedral angles, the joint comparison-angle limit, the full eight-plane tetrahedron realization, inverse arbitrary tetrahedron realization and rigidity, volume, gluing and genus remain outside this theorem. The full four-source CFMP goal, sections 1-125 including 42.3 and 122.3, is not completed here.

## References

- Truth anchor: `D5/S3/Geometry/HyperbolicPlaneRealization.supporting_plane_isometry`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramMetricSegments](Hyperideal/LengthGramMetricSegments.md)

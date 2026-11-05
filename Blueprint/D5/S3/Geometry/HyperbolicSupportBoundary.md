# Finite support regions in an actual hyperbolic plane

## Abstract

Complete interiors and frontiers of finite Lorentz support regions.

Let H2 be UpperHalfPlane with its hyperbolic metric, H3 be HyperbolicThreeSpace with its original metric, and B be the Lorentz form on R4 with signature (1,1,1,-1). Phi is the original LengthGramMetricSegments.lift. For a map e:H2 -> H3 and a finite family A:I -> R4, write L(e,A,i,z)=B(A(i),Phi(e(z))). The set R(e,A) is exactly {z in H2 : for every i in I, L(e,A,i,z)<=0}; this is supportRegion e A. Write Strict(e,A) for the set where all these inequalities are strict, and Active(e,A) for {z in R(e,A) : there exists i in I with L(e,A,i,z)=0}. Pi(N) is {p in H3 : B(N,Phi(p))=0}. Interior and Frontier below are taken in the whole H2 topology.

**Theorem 1.1 (Strict supports describe the interior and active supports the frontier).**

$$\forall I \in Types,\; Finite\left(I\right) \Rightarrow \left(\forall e \in Maps\left(H2, H3\right),\; \forall N \in R4,\; \forall A \in Maps\left(I, R4\right),\; \left(Isometry\left(e\right) \land \left(Range\left(e\right) = Pi\left(N\right) \land \left(\forall i \in I,\; \exists y \in H2,\; Contains\left(R\left(e, A\right), y\right) \land L\left(e, A, i, y\right) < 0\right)\right)\right) \Rightarrow \left(Interior\left(R\left(e, A\right)\right) = Strict\left(e, A\right) \land Frontier\left(R\left(e, A\right)\right) = Active\left(e, A\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/HyperbolicSupportBoundary.support_region_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James W. Cannon, William J. Floyd, Richard Kenyon, and Walter R. Parry (1997). *Hyperbolic Geometry*. URL: <https://library.slmath.org/books/Book31/files/cannon.pdf>.

*Commentary.*

Assume e is an isometry whose complete range is Pi(N). For each i require a point y in this same R(e,A) with L(e,A,i,y)<0. The points may differ with i. Then the full interior is Strict(e,A), and the full frontier is Active(e,A). The finite index type may be empty: both R and Strict are then all of H2 and Active is empty. No normalization of N or A is required. The exact plane range and strict points are hypotheses.

Suppose L(e,A,i,x)=0 and choose the required strict y. Set Y=Phi(e(x)), Z=Phi(e(y)), d=dist(e(x),e(y)) and U=(-cosh(d)/sinh(d))*Y+(1/sinh(d))*Z. The unequal readouts give d>0. The lift distance identity and the unit equations give B(Y,U)=0 and B(U,U)=1. The original global metric-line construction gives an isometry g from the real line with g(0)=e(x) and Phi(g(t))=cosh(t)*Y+sinh(t)*U.

Both Y and Z are orthogonal to N. Consequently U and every Phi(g(t)) are orthogonal to N, so the exact range condition pulls g back to a continuous curve c in H2 through x. Its i-th support readout is sinh(t)*L(e,A,i,y)/sinh(d), which is strictly positive for every t<0. Every neighborhood of x therefore contains a point outside R(e,A). This excludes any active equality from the interior. Conversely, finitely many continuous strict inequalities define an open subset of R(e,A). Continuity of the weak inequalities makes R closed; subtracting its interior gives precisely the displayed frontier.

The Lorentz distance and geodesic ingredients are classical, as in the cited source's projective-model discussion on page 80 and its distance identity on page 83. The finite-support boundary criterion above is derived from these ingredients and elementary topology; no novelty is claimed. Its application to an original polygon requires the complete plane, the same region and the stated strict points. Identifying that frontier with a particular cyclic list of metric segments requires the corresponding complete support traces. A polygon's disk topology and a length-domain characterization are further conclusions.

## References

- Truth anchor: `D5/S3/Geometry/HyperbolicSupportBoundary.support_region_boundary`
- Dependency: [D5/S3/Geometry/HyperbolicTopology](HyperbolicTopology.md)
- Dependency: [D5/S3/Geometry/Hyperideal/ActualRaysJointAngle](Hyperideal/ActualRaysJointAngle.md)

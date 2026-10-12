# Unit tangent rays in the original hyperbolic metric

## Abstract

Actual hyperbolic rays and their joint comparison angle.

Let Rfour be the real four-coordinate space, and let B be the space-positive, time-negative Lorentz form. Hthree is the original HyperbolicThreeSpace with its hyperbolic distance. Psi is the original project map: its horizontal coordinate is (Y0+i*Y1)/(Y3-Y2) and its height is 1/(Y3-Y2). Phi is the original inverse lift. The theorem ranges over every future unit Y and every pair U,V of Lorentz-unit vectors orthogonal to Y, with B(U,V) in the closed interval [-1,1].

Write W(Y,U,t)=cosh(t)Y+sinh(t)U, C(c,s,t)=cosh(s)cosh(t)-c sinh(s)sinh(t), and K(g,h,s,t)=(s*s+t*t-dist(g(s),h(t))^2)/(2*s*t). Angle(g,h) is the function (s,t) mapped to arccos(K(g,h,s,t)). Q is the product of the two strictly positive real half-lines; NQ is the neighborhood filter at (0,0) within Q. It is a nontrivial filter and equals the product of the two right-hand neighborhood filters. No restriction is imposed on the ratio of the parameters.

**Theorem 1.1 (Global metric lines and the unrestricted joint limit).**

$$\forall Y \in Rfour,\; \forall U \in Rfour,\; \forall V \in Rfour,\; \left(B\left(Y, Y\right) = -1 \land \left(0 < coord\left(Y, 3\right) \land \left(B\left(U, U\right) = 1 \land \left(B\left(V, V\right) = 1 \land \left(B\left(Y, U\right) = 0 \land \left(B\left(Y, V\right) = 0 \land \left(-1 \le B\left(U, V\right) \land B\left(U, V\right) \le 1\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists g \in Maps\left(R, Hthree\right),\; \exists h \in Maps\left(R, Hthree\right),\; Isometry\left(g\right) \land \left(Isometry\left(h\right) \land \left(apply\left(g, 0\right) = Psi\left(Y\right) \land \left(apply\left(h, 0\right) = Psi\left(Y\right) \land \left(\left(\forall t \in R,\; Phi\left(apply\left(g, t\right)\right) = W\left(Y, U, t\right)\right) \land \left(\left(\forall t \in R,\; Phi\left(apply\left(h, t\right)\right) = W\left(Y, V, t\right)\right) \land \left(\left(\forall s \in R,\; \forall t \in R,\; cosh\left(dist\left(apply\left(g, s\right), apply\left(h, t\right)\right)\right) = C\left(B\left(U, V\right), s, t\right)\right) \land \left(\left(\forall s \in R,\; \forall t \in R,\; \left(0 \le s \land 0 \le t\right) \Rightarrow \left(abs\left(s-t\right) \le dist\left(apply\left(g, s\right), apply\left(h, t\right)\right) \land dist\left(apply\left(g, s\right), apply\left(h, t\right)\right) \le s+t\right)\right) \land Tendsto\left(Angle\left(g, h\right), NQ, nhds\left(arccos\left(B\left(U, V\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/ActualRaysJointAngle.actual_rays_joint_angle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Octavian Ganea, Gary Becigneul, and Thomas Hofmann (2018). *Hyperbolic Entailment Cones for Learning Hierarchical Embeddings*. URL: <https://proceedings.mlr.press/v80/ganea18a.html>.

*Commentary.*

Spatial Cauchy-Schwarz applied to the unit and orthogonality equations gives U3^2 <= Y3^2-1 and hence abs(U3)<Y3. Since abs(sinh(t))<cosh(t), W(Y,U,t) has positive time for every real t. Bilinearity gives B(W,W)=-1. Therefore Psi(W) is defined on the whole real line and Phi(Psi(W))=W. The original metric identity B(Phi(p),Phi(q))=-cosh(dist(p,q)) gives the two-ray distance law. For equal tangent directions, injectivity of cosh on nonnegative reals gives dist(g(s),g(t)) =abs(s-t), proving an actual isometry from the real line.

Put D=dist(g(s),h(t)), q=abs(s-t), A=(D+q)/2 and E=(D-q)/2. The metric triangle inequalities give q<=D<=s+t for nonnegative s,t. Define S(x)=dslope(sinh,0,x); thus S(0)=1, x*S(x)=sinh(x), and S is continuous at zero. For positive s,t, the cosh distance law and the addition identities give K=1-(1-c)S(s)S(t)/(S(A)S(E)). The denominator is positive, including E=0. Metric continuity makes A,E tend jointly to zero, so this expression extends continuously with value c at the origin. Continuity of arccos gives the stated angle limit, including c=1 and c=-1. The proof never divides by D, A, E or 1-c; D=0 is included.

For the original Section 66 radial realization, Y is the lift of a point of the same image and tangent directions must satisfy the displayed unit and orthogonality conditions. This result provides metric rays and their angle. It does not identify inward face germs or recover the original body from supporting halfspaces. Normal normalization, same-body face membership, and the six original and twelve truncation dihedral angles remain separate mathematical obligations. The full realization problem retains all six positive lengths and all six strict source cosine conditions.

The classical cosh-sinh ray formula is recorded in Appendix A, Theorem 6, equation (38) of the cited supplement on [0,1], with time-first coordinates. The construction here establishes the global original-metric contract and derives the joint limit directly; it makes no novelty claim for the classical geometry.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/ActualRaysJointAngle.actual_rays_joint_angle`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramMetricSegments](LengthGramMetricSegments.md)

# The original coefficient segment and every ambient between-point

## Abstract

Metric segments of the same frozen six-length radial body.

Fix the six strictly positive lengths l in the original order (01,02,03,23,13,12). C(l), q(l,v), radial(l,v), and the space-positive, time-negative Lorentz form B are exactly LengthGramBody's definitions. Keep one concrete matrix m and one injective map f from C(l) into the actual hyperbolic upper half-space H3. No replacement congruent tetrahedron is chosen. The displayed radial-coordinate condition is precisely the supplied witness; Psi(y) has horizontal coordinate (y0+i*y1)/(y3-y2) and height 1/(y3-y2). Positive time is part of the contract, and all distances below are the hyperbolic metric on HyperbolicThreeSpace, not the Euclidean coordinate metric.

For lambda,mu in C(l), write D=dist(f(lambda),f(mu)). ImageSegment(l,f,lambda,mu) is the set of all f(v), where v is in C(l) and its original coefficient vector belongs to the closed affine segment [lambda,mu]. Between(p,q) is the set of every ambient z in H3 satisfying dist(p,z)+dist(z,q)=dist(p,q). Maps denotes ordinary functions and Icc the closed real interval with its usual metric. R6, R4 and Matrix4 denote the real six-coordinate space, four-coordinate space and four-by-four matrices.

**Theorem 1.1 (An actual isometric interval with both exact range identifications).**

$$\forall l \in R6,\; \left(\forall k \in Fin\left(6\right),\; 0 < coord\left(l, k\right)\right) \Rightarrow \left(\forall m \in Matrix4,\; \forall f \in Maps\left(C\left(l\right), H3\right),\; \left(Injective\left(f\right) \land \left(\forall v \in C\left(l\right),\; \exists y \in R4,\; y = vecMul\left(radial\left(l, v\right), m\right) \land \left(B\left(y, y\right) = -1 \land \left(0 < coord\left(y, 3\right) \land coordinates\left(apply\left(f, v\right)\right) = Psi\left(y\right)\right)\right)\right)\right) \Rightarrow \left(\forall lambda \in C\left(l\right),\; \forall mu \in C\left(l\right),\; \exists gamma \in Maps\left(Icc\left(0, dist\left(apply\left(f, lambda\right), apply\left(f, mu\right)\right)\right), H3\right),\; Isometry\left(gamma\right) \land \left(apply\left(gamma, 0\right) = apply\left(f, lambda\right) \land \left(apply\left(gamma, dist\left(apply\left(f, lambda\right), apply\left(f, mu\right)\right)\right) = apply\left(f, mu\right) \land \left(range\left(gamma\right) = ImageSegment\left(l, f, lambda, mu\right) \land range\left(gamma\right) = Between\left(apply\left(f, lambda\right), apply\left(f, mu\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.same_body_metric_segments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James W. Cannon, William J. Floyd, Richard Kenyon, and Walter R. Parry (1997). *Hyperbolic Geometry*. URL: <https://library.slmath.org/books/Book31/files/cannon.pdf>.

*Commentary.*

For different endpoints let X and Y be their future unit Lorentz lifts. At arclength t take Gamma(t)=sinh(D-t)/sinh(D)*X +sinh(t)/sinh(D)*Y and project by Psi. The inverse upper-half-space coordinates are (x/h,y/h,(x*x+y*y+h*h-1)/(2*h), (x*x+y*y+h*h+1)/(2*h)). The existing sinh half-distance theorem gives B(lift(p),lift(q))=-cosh(dist(p,q)). Hyperbolic addition identities then give B(Gamma(s),Gamma(t))=-cosh(s-t). The interpolation has positive time, and strict monotonicity of cosh on nonnegative reals proves the isometry.

For any ambient between-point z put t=dist(p,z). Its lift and Gamma(t) have the same pairings with X and Y. Their difference is Lorentz-null and orthogonal to the unit timelike vector X. The pinned finite-sum Cauchy-Schwarz theorem forces this difference to vanish. Inverse-coordinate injectivity therefore identifies z with the interpolated point. This proves full ambient rigidity, including the two endpoints.

The original affine-segment coverage uses exactly the same m and f. Put r(v)=sqrt(-q(l,v)), a(t)=sinh(D-t)/(sinh(D)*r(lambda)), b(t)=sinh(t)/(sinh(D)*r(mu)), and w(t)=b(t)/(a(t)+b(t)). Frozen negativity makes both endpoint radii positive. Frozen cut_body_polytope supplies convexity through its convex-hull equality. Thus nu(t)=(1-w(t))*lambda+w(t)*mu lies in the original segment. Linearity of multiplication by m identifies its lift with a positive multiple of Gamma(t); both lifts have Lorentz norm -1, so that multiple is one. The continuous weight w runs from zero to one, and the intermediate value theorem supplies every original affine-segment point. The affine weight generally differs from arclength divided by D. Equal endpoints are treated separately by the constant map from the singleton interval.

This is a geometric prerequisite to original section 66, using unchanged shared_radial_body and cut_body_polytope suppliers. The theorem quantifies over any witnesses of the displayed exact contract, so it includes irregular admissible lengths and boundary points. Its conditional segment statement needs no additional cosine assumptions once the witnesses are supplied. The original full-source realization domain still requires all six strict source cosine inequalities; the one inequality used by the frozen frame supplier does not establish the remaining geometry. No full-source realization wrapper is exported here.

The acknowledged source supplies the classical unique-geodesic, Klein/hyperboloid projective, and Lorentz-distance ingredients (Theorem 9.3 and the discussion through page 80; Section 10, Theorem 10.1 on page 82 and the distance lemma on page 83). The exact application to the frozen cutBody and radial definitions, with the same m and f and both displayed range identities, is a repository derivation rather than a theorem stated verbatim in that source. No mathematical novelty claim is made. Eight actual geodesic halfspaces and three-dimensional interior, four triangle and four hexagon face incidence, prescribed original edge lengths, actual dihedral angles and orthogonal truncation, permutation isometries, inverse source realization and rigidity, volume, Schlaefli theory and global CFMP gluing remain separate obligations.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LengthGramMetricSegments.same_body_metric_segments`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramPolytope](LengthGramPolytope.md)

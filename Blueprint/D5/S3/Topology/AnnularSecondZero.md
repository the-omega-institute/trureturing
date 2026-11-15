# A second zero from the sphere obstruction

## Abstract

A regular zero forces another zero when the exterior is constant or both annular boundaries lie in a strict half-plane.

All derivatives in this document are Frechet derivatives over the real field. ContinuousLinearEquiv denotes an invertible continuous real linear map, and toContinuousLinearMap is its underlying derivative operator. The norm is the given real norm; no inner product is needed in the first result.

**Theorem 1.1 (A constant exterior cannot enclose just one regular zero).**

$$\forall E \in Types,\; [NormedAddCommGroup\left(E\right)] [NormedSpace\left(Real, E\right)] [FiniteDimensional\left(Real, E\right)] [Nontrivial\left(E\right)] \forall q \in E \to E,\; \forall a \in E,\; \forall c \in E,\; \forall M \in Real,\; \forall L \in ContinuousLinearEquiv\left(Real, E, E\right),\; \left(Continuous\left(q\right) \land \left(c \neq 0 \land \left(\left(\forall x \in E,\; M \le norm\left(x\right) \Rightarrow q\left(x\right) = c\right) \land \left(q\left(a\right) = 0 \land HasFDerivAt\left(q, toContinuousLinearMap\left(L\right), a\right)\right)\right)\right)\right) \Rightarrow \left(\exists b \in E,\; b \neq a \land q\left(b\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/AnnularSecondZero.constantExterior_second_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be any nontrivial finite-dimensional real normed space, q a continuous map E to E, and a and c points of E with c nonzero. The real threshold M is arbitrary. Assume q(x)=c whenever M is at most norm(x), q(a)=0, and the ordinary derivative of q at a is the invertible continuous linear map L. Then q has a zero b distinct from a.

Compose q with the inverse of L. Its derivative at a is the identity, so the derivative remainder gives norm(p(a+h)-h) at most norm(h)/2 on a sufficiently small closed ball. On its boundary the straight segment from h to p(a+h) never vanishes. Normalizing that segment gives a homotopy from the unit-sphere identity to the normalized local image.

If a were the only zero, expand the positive sphere radius about a until every image point lies in the constant exterior. The normalized image would then be homotopic to a constant. Joining these homotopies contracts the unit sphere, contradicting TauCeti.not_contractibleSpace_sphere. This includes ambient dimension one and uses only the ordinary derivative at the designated point.

**Theorem 1.2 (Two left-half-plane boundary circles force a second interior zero).**

$$\forall f \in Complex \to Complex,\; \forall a \in Complex,\; \forall r \in Real,\; \forall R \in Real,\; \forall L \in ContinuousLinearEquiv\left(Real, Complex, Complex\right),\; \left(0 < r \land \left(r < norm\left(a\right) \land \left(norm\left(a\right) < R \land \left(ContinuousOn\left(f, SetDifference\left(closedBall\left(0, R\right), ball\left(0, r\right)\right)\right) \land \left(f\left(a\right) = 0 \land \left(HasFDerivAt\left(f, toContinuousLinearMap\left(L\right), a\right) \land \left(\forall z \in Complex,\; \left(norm\left(z\right) = r \lor norm\left(z\right) = R\right) \Rightarrow re\left(f\left(z\right)\right) < 0\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists b \in Complex,\; r < norm\left(b\right) \land \left(norm\left(b\right) < R \land \left(b \neq a \land f\left(b\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/AnnularSecondZero.annular_second_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map f is a total function on the complex plane, with continuity required only on closedBall(0,R) minus ball(0,r). SetDifference denotes this set difference. The radii satisfy 0<r<norm(a)<R. The point a is a zero with invertible real derivative L. On each of the two boundary circles, the real part of f is strictly negative. The conclusion gives b with r<norm(b)<R, b distinct from a, and f(b)=0.

Write rho=norm(z), and radially clamp rho to the interval from r to R. Multiply f of that clamped point by w, where w is the product of clamp(2 rho/r-1) and clamp(R+1-rho), and clamp(t)=max(0,min(1,t)). Add (1-w) times minus one. The resulting map q agrees with f on the closed annulus, equals minus one for rho at most r/2 or at least R+1, and is continuous everywhere.

Away from zero the radial clamp and the weights are continuous and the clamped point stays in the closed annulus, including all seams. Near zero the weight vanishes and q is constant, so no division at zero enters the continuity argument. On an inner or outer collar the clamped point lies on the corresponding boundary circle. Both f of that point and minus one have negative real part, so their convex combination is nonzero.

Because a is strictly interior, q agrees with f on a neighborhood of a and inherits its ordinary real derivative. Apply the constant-exterior result. Every zero of q lies strictly in the original annulus, so its second zero is a second zero of f there. No holomorphicity, strict differentiability, isolated-zero condition or finiteness of other zeros is assumed.

These are static topological consequences of the classical sphere obstruction, with no originality claim. Applying them to a reconstruction residual still requires an actual residual, its continuity, the two boundary inequalities, an interior zero and its invertible real derivative. They provide no dynamics, time group, energy, physical clock or thermodynamic conclusion.

## References

- Truth anchor: `D5/S3/Topology/AnnularSecondZero.annular_second_zero`
- Truth anchor: `D5/S3/Topology/AnnularSecondZero.constantExterior_second_zero`

# Fixed original spheres do not collapse

## Abstract

Binary compatibility gives sphere-center Lipschitz bounds and an attained positive diameter bound for each fixed original sphere.

V, C, u, K, P, all original proper effects and the full original exclusion D(p) have the same meanings as in BinaryCenterGeometry. Closedness, strict positivity on every nonzero cone vector and generating span are retained. B is an actual proof of exclusionBalls, and center is the existing ContinuousFrameSum.center. ExclusionChart parametrizes the whole original ball by an injective affine map of a positive-dimensional Euclidean closed unit ball. sphereCenter(B,p,b) is the function on that chart's unit sphere taking x to center(B,chartPure(p,b,x)); chartPure is the original SingleLabelNormalBody owner. No global center continuity, closed pure locus, global injectivity or width-one premise is used.

**Theorem 1.1 (A direct original BC estimate).**

$$\forall V \in Types,\; [NormedAddCommGroup\left(V\right)] [NormedSpace\left(Real, V\right)] [FiniteDimensional\left(Real, V\right)] \forall C \in PointedCone\left(Real, V\right),\; \forall u \in LinearMaps\left(Real, V, Real\right),\; \left(IsClosed\left(C\right) \land \left(\left(\forall x \in V,\; \left(x \in C \land x \ne 0\right) \Rightarrow 0 < u\left(x\right)\right) \land span\left(Real, C\right) = top\right)\right) \Rightarrow \left(\forall B \in exclusionBalls\left(C, u\right),\; binaryCompatible\left(B\right) \Rightarrow \left(\forall p \in pure\left(C, u\right),\; \forall b \in ExclusionChart\left(C, u, p\right),\; LipschitzWith\left(\frac{diam\left(base\left(C, u\right)\right)}{2}, sphereCenter\left(B, p, b\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.sphere_center_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two distinct unit chart vectors x and y, let d=norm(x-y), k=(x-y)/d and v=(2+d)/4. Then 0<d<=2 and v lies in the closed unit interval. The midpoint of x and -y equals v k+(1-v)(-k), while the antipodal midpoints of y,-y and k,-k agree. Apply original BC to both equalities after the same original whole-ball chart. Subtraction gives c(x)-c(y)=(d/2)(c(k)-c(-k)). Both centers lie in the original compact K, so their distance is at most diam(K). Thus the sphere-center map is Lipschitz with constant diam(K)/2. Equal chart vectors are handled directly. The proof needs only whole positive-dimensional balls and applies, in particular, to EB3.

**Theorem 1.2 (Attainment, strict positivity, diameter bound and avoidance).**

$$\forall V \in Types,\; [NormedAddCommGroup\left(V\right)] [NormedSpace\left(Real, V\right)] [FiniteDimensional\left(Real, V\right)] \forall C \in PointedCone\left(Real, V\right),\; \forall u \in LinearMaps\left(Real, V, Real\right),\; \left(IsClosed\left(C\right) \land \left(\left(\forall x \in V,\; \left(x \in C \land x \ne 0\right) \Rightarrow 0 < u\left(x\right)\right) \land span\left(Real, C\right) = top\right)\right) \Rightarrow \left(\forall H \in threeBallExclusions\left(C, u\right),\; binaryCompatible\left(threeImpliesBalls\left(H\right)\right) \Rightarrow \left(\forall p \in pure\left(C, u\right),\; \exists delta \in Real,\; 0 < delta \land \left(\left(\exists z \in pure\left(C, u\right),\; z \in exclusion\left(C, u, p\right) \land \left(delta = twiceDistance\left(p, center\left(threeImpliesBalls\left(H\right), z\right)\right) \land \left(\forall q \in pure\left(C, u\right),\; q \in exclusion\left(C, u, p\right) \Rightarrow delta \le twiceDistance\left(p, center\left(threeImpliesBalls\left(H\right), q\right)\right)\right)\right)\right) \land \left(\left(\forall q \in pure\left(C, u\right),\; q \in exclusion\left(C, u, p\right) \Rightarrow delta \le diam\left(exclusion\left(C, u, q\right)\right)\right) \land \left(\forall a \in Functions\left(Nat, pure\left(C, u\right)\right),\; diametersTendToZero\left(C, u, a\right) \Rightarrow eventuallyAvoids\left(C, u, p, a\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.fixed_sphere_noncollapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

H is the original threeBallExclusions premise, and threeImpliesBalls(H) is the exposed original CommonOldExclusionConfirmation.three_implies_balls. twiceDistance(p,c) means 2 norm(p-c). diametersTendToZero(C,u,a) means that diam(D(a(n))) tends to zero along the natural numbers, and eventuallyAvoids(C,u,p,a) means that all sufficiently late original labels a(n) lie outside D(p). Because those labels are already original pure points, this is precisely eventual avoidance of S(D(p)). The existential delta is inside the quantifier over the fixed original p.

The preceding Lipschitz theorem makes the original center restriction continuous on the compact chart sphere. Original chart_boundary identifies its image labels with every original pure point of the whole fixed ball, so a minimum distance to p is attained. The centerSection theorem says each original center is nonpure; it cannot equal the pure p. Hence the attained minimum is strictly positive. Delta is twice that actual minimum, with its minimizer and universal minimum inequality both stated explicitly.

For every original q on this fixed sphere, zero symmetry puts p in D(q). The unchanged original old_geometry owner reflects p within the same whole D(q). Existing affine-ball center uniqueness identifies its oldCenter with ContinuousFrameSum.center. The two points have distance exactly 2 norm(p-c(q)), giving the diameter bound. Eventually a sequence of diameters tending to zero is below this fixed delta, which excludes each late label from the fixed sphere. Constants for different fixed balls are quantified separately. This proves no uniform lower bound over all balls and no full-axis inner ball.

The minimum statement uses only the boundary value c(q), which is exactly the boundary value prescribed for G_F in XI138.2; its distance formula is therefore the original XI138.5 formula without assuming that the missing whole-ball affine map has already been constructed. The local graph, its rank dichotomy, exact sections and reflected-ball alternatives remain separate unresolved obligations. No BC to MC, global injectivity, quantum classification, physical realization or literature-priority claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.fixed_sphere_noncollapse`
- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.sphere_center_lipschitz`
- Dependency: [D5/S3/Quantum/Foundation/BinaryCenterGeometry](BinaryCenterGeometry.md)
- Dependency: [D5/S3/Quantum/Foundation/CommonOldExclusionConfirmation](CommonOldExclusionConfirmation.md)

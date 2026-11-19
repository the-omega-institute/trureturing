# Whole-ball center graphs and fixed original spheres

## Abstract

Binary compatibility determines each whole-ball affine center graph, its rank branches and singleton section, as well as fixed-sphere quantitative bounds.

V, C, u, K, P, all original proper effects and the full original exclusion D(p) have the same meanings as in BinaryCenterGeometry. Closedness, strict positivity on every nonzero cone vector and generating span are retained. B is an actual proof of exclusionBalls, and center is the existing ContinuousFrameSum.center. ExclusionChart parametrizes the whole original ball by an injective affine map of a positive-dimensional Euclidean closed unit ball. sphereCenter(B,p,b) is the function on that chart's unit sphere taking x to center(B,chartPure(p,b,x)); chartPure is the original SingleLabelNormalBody owner. No global center continuity, closed pure locus, global injectivity or width-one premise is used.

**Theorem 1.1 (The unique affine graph on every whole source ball).**

Lean statement: `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.whole_ball_center_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.whole_ball_center_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original domain described above, every proof B of exclusionBalls satisfying the complete original binaryCompatible law, every original pure p and every entire ExclusionChart b of D(p), there exists exactly one real affine map g from the Euclidean chart carrier to V with g(x)=center(B,chartPure(p,b,x)) for every unit vector x, and its entire closed unit ball image is contained in K. The unique map is on the source chart carrier, equivalently on the affine span of the whole original D(p). No uniqueness on all of V is asserted. Since b is injective and its whole closed ball image is D(p), g composed with the inverse chart defines the actual G_F on every point of F=D(p); the sphere is exactly all original pure points of F.

Coordinate reflections preserve the chart sphere. Comparing their original chords by BC gives the change in the center function when one coordinate is reversed. Telescoping over all coordinates and using the common antipodal midpoint determines an affine interpolant with explicit basis coefficients. This constructs the map on the whole chart carrier from the actual original centers. Sphere convex generation and convexity of K give its entire-ball range; affine spanning gives uniqueness.

**Theorem 1.2 (Repeated and singleton rank branches).**

Lean statement: `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.whole_ball_center_graph`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.whole_ball_center_graph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every same original domain, B, BC, pure p and entire chart b, there exists an affine g with all the preceding original boundary values and entire-ball range K, unique among all affine maps with those boundary values. If SingleLabel(C,u,p), g is injective and its linear range has dimension b.dim. If SingleLabel fails, g is constant on the entire chart carrier. For an actual three-dimensional original chart the derived rank is therefore three, without an assumed rank certificate.

A nonzero kernel vector would give two distinct antipodal source sphere points with the same original center. Their exclusions share this nonpure point; the original extreme-face intersection and two-point rigidity force equality of their whole exclusions. Singleton-label propagation on the original sphere then identifies the two pure points, a contradiction. In the repeated case, the full reciprocal fibers identify every sphere label's entire exclusion with the opposite ball. Whole-ball center uniqueness and sphere affine spanning force g to be constant.

**Theorem 1.3 (Every interior image point and the exact section).**

Lean statement: `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.whole_ball_center_section`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.whole_ball_center_section` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every same original domain, B and BC, every original pure p with SingleLabel(C,u,p), and every entire chart b, there exists an affine g with the actual original center boundary values, injective with linear range dimension b.dim, sending every chart vector of norm strictly below one into the relative interior of K. Its entire closed unit ball image is exactly K intersect the affine range of g. This affine range is the affine span of that entire image, since the source closed unit ball affinely spans the chart carrier. For every original sphere label q the linear range of g is disjoint from the chosen whole D(q) chart linear range, equivalently the direction of D(q) translated to its center. A common direction would yield two distinct points in the exact section with midpoint c(q), contradicting its extremeness in the image ball.

If an interior image point belonged to the original relative boundary, frontier coverage and an original exposing effect would give a nonnegative affine function vanishing at an interior source point. The original affine_zero_inside_ball owner makes it vanish on all source vectors. Each boundary center then forces its entire original exclusion into that same exposed face. Original whole-face maximality identifies every such exclusion, so g would be constant on its sphere, contradicting injectivity. For the exact section, any K point in the affine range but beyond the image ball would put a sphere-center boundary point on an open segment from the interior image center to that K point. The intrinsic interior segment theorem gives a contradiction.

**Theorem 1.4 (Relative frontier of an injective affine ball).**

Lean statement: `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.affine_ball_frontier`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.affine_ball_frontier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite dimensional real inner product source E with at least two points, every finite dimensional real normed target V and every injective real affine g:E to V, the intrinsic frontier of g(closedBall(0,1)) is exactly g(sphere(0,1)). Compactness makes the image closed; intrinsic interior transport identifies the removed open ball. This supplies the entire image sphere in the original center and reflected-ball conclusions.

**Theorem 1.5 (The original three-dimensional sections and dimension bound).**

Lean statement: `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.original_center_sections`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.original_center_sections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the same closed pointed generating original cone, strict unit, nonzero finite dimensional real carrier, original EB3 and the complete original BC law. The affine dimension of the whole K is at least six and an original singleton-label exclusion exists. For every singleton-label original p there are an entire three-dimensional chart b of D(p) and an affine g with every original center boundary value, injective with linear rank three, sending every norm-below-one source point into the intrinsic interior of K. Its entire closed-ball image equals K intersect its own affine span. Its entire intrinsic frontier equals its sphere image, all those sphere-center points lie on the original intrinsic frontier of K, and its linear range is disjoint from every corresponding whole original exclusion direction. Native singleton-ball dimension bounds and the normalized-base dimension identity are applied to the same original V,C,u. The dimension conclusion has no physical-realization implication.

**Theorem 1.6 (A direct original BC estimate).**

$$\forall V \in Types,\; [NormedAddCommGroup\left(V\right)] [NormedSpace\left(Real, V\right)] [FiniteDimensional\left(Real, V\right)] \forall C \in PointedCone\left(Real, V\right),\; \forall u \in LinearMaps\left(Real, V, Real\right),\; \left(IsClosed\left(C\right) \land \left(\left(\forall x \in V,\; \left(x \in C \land x \ne 0\right) \Rightarrow 0 < u\left(x\right)\right) \land span\left(Real, C\right) = top\right)\right) \Rightarrow \left(\forall B \in exclusionBalls\left(C, u\right),\; binaryCompatible\left(B\right) \Rightarrow \left(\forall p \in pure\left(C, u\right),\; \forall b \in ExclusionChart\left(C, u, p\right),\; LipschitzWith\left(\frac{diam\left(base\left(C, u\right)\right)}{2}, sphereCenter\left(B, p, b\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.sphere_center_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two distinct unit chart vectors x and y, let d=norm(x-y), k=(x-y)/d and v=(2+d)/4. Then 0<d<=2 and v lies in the closed unit interval. The midpoint of x and -y equals v k+(1-v)(-k), while the antipodal midpoints of y,-y and k,-k agree. Apply original BC to both equalities after the same original whole-ball chart. Subtraction gives c(x)-c(y)=(d/2)(c(k)-c(-k)). Both centers lie in the original compact K, so their distance is at most diam(K). Thus the sphere-center map is Lipschitz with constant diam(K)/2. Equal chart vectors are handled directly. The proof needs only whole positive-dimensional balls and applies, in particular, to EB3.

**Theorem 1.7 (Attainment, strict positivity, diameter bound and avoidance).**

$$\forall V \in Types,\; [NormedAddCommGroup\left(V\right)] [NormedSpace\left(Real, V\right)] [FiniteDimensional\left(Real, V\right)] \forall C \in PointedCone\left(Real, V\right),\; \forall u \in LinearMaps\left(Real, V, Real\right),\; \left(IsClosed\left(C\right) \land \left(\left(\forall x \in V,\; \left(x \in C \land x \ne 0\right) \Rightarrow 0 < u\left(x\right)\right) \land span\left(Real, C\right) = top\right)\right) \Rightarrow \left(\forall H \in threeBallExclusions\left(C, u\right),\; binaryCompatible\left(threeImpliesBalls\left(H\right)\right) \Rightarrow \left(\forall p \in pure\left(C, u\right),\; \exists delta \in Real,\; 0 < delta \land \left(\left(\exists z \in pure\left(C, u\right),\; z \in exclusion\left(C, u, p\right) \land \left(delta = twiceDistance\left(p, center\left(threeImpliesBalls\left(H\right), z\right)\right) \land \left(\forall q \in pure\left(C, u\right),\; q \in exclusion\left(C, u, p\right) \Rightarrow delta \le twiceDistance\left(p, center\left(threeImpliesBalls\left(H\right), q\right)\right)\right)\right)\right) \land \left(\left(\forall q \in pure\left(C, u\right),\; q \in exclusion\left(C, u, p\right) \Rightarrow delta \le diam\left(exclusion\left(C, u, q\right)\right)\right) \land \left(\forall a \in Functions\left(Nat, pure\left(C, u\right)\right),\; diametersTendToZero\left(C, u, a\right) \Rightarrow eventuallyAvoids\left(C, u, p, a\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.fixed_sphere_noncollapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

H is the original threeBallExclusions premise, and threeImpliesBalls(H) is the exposed original CommonOldExclusionConfirmation.three_implies_balls. twiceDistance(p,c) means 2 norm(p-c). diametersTendToZero(C,u,a) means that diam(D(a(n))) tends to zero along the natural numbers, and eventuallyAvoids(C,u,p,a) means that all sufficiently late original labels a(n) lie outside D(p). Because those labels are already original pure points, this is precisely eventual avoidance of S(D(p)). The existential delta is inside the quantifier over the fixed original p.

The preceding Lipschitz theorem makes the original center restriction continuous on the compact chart sphere. Original chart_boundary identifies its image labels with every original pure point of the whole fixed ball, so a minimum distance to p is attained. The centerSection theorem says each original center is nonpure; it cannot equal the pure p. Hence the attained minimum is strictly positive. Delta is twice that actual minimum, with its minimizer and universal minimum inequality both stated explicitly.

For every original q on this fixed sphere, zero symmetry puts p in D(q). The unchanged original old_geometry owner reflects p within the same whole D(q). Existing affine-ball center uniqueness identifies its oldCenter with ContinuousFrameSum.center. The two points have distance exactly 2 norm(p-c(q)), giving the diameter bound. Eventually a sequence of diameters tending to zero is below this fixed delta, which excludes each late label from the fixed sphere. Constants for different fixed balls are quantified separately. This proves no uniform lower bound over all balls and no full-axis inner ball.

The minimum statement uses the boundary value c(q), now realized by the whole-ball affine graph. Constants for different fixed balls remain separately quantified. The reflected-ball alternatives and global connections require their own conclusions. No BC to MC, global injectivity, uniform noncollapse, quantum classification, physical realization or literature-priority claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.affine_ball_frontier`
- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.fixed_sphere_noncollapse`
- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.original_center_sections`
- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.sphere_center_lipschitz`
- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.whole_ball_center_affine`
- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.whole_ball_center_graph`
- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.whole_ball_center_section`
- Dependency: [D5/S3/Quantum/Foundation/BinaryCenterGeometry](BinaryCenterGeometry.md)
- Dependency: [D5/S3/Quantum/Foundation/CommonOldExclusionConfirmation](CommonOldExclusionConfirmation.md)
- Dependency: [D5/S3/Quantum/Foundation/CommonSourceLiftObstruction](CommonSourceLiftObstruction.md)

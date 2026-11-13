# The actual boundary and common whole exclusions

## Abstract

Whole original exclusions cover the actual relative boundary and detect its boundary midpoints.

**Theorem 1.1 (Boundary coverage and the midpoint criterion).**

$$\forall V \in Types,\; [NormedAddCommGroup\left(V\right)] [NormedSpace\left(Real, V\right)] [FiniteDimensional\left(Real, V\right)] \forall C \in PointedCone\left(Real, V\right),\; \forall u \in LinearMaps\left(Real, V, Real\right),\; \left(IsClosed\left(C\right) \land \left(\left(\forall x \in V,\; \left(x \in C \land x \ne 0\right) \Rightarrow 0 < u\left(x\right)\right) \land \left(span\left(Real, C\right) = top \land exclusionBalls\left(C, u\right)\right)\right)\right) \Rightarrow \left(\left(\forall x \in V,\; x \in intrinsicFrontier\left(Real, base\left(C, u\right)\right) \Rightarrow \left(\exists p \in pure\left(C, u\right),\; x \in exclusion\left(C, u, p\right)\right)\right) \land \left(\forall x \in V,\; x \in base\left(C, u\right) \Rightarrow \left(\forall y \in V,\; y \in base\left(C, u\right) \Rightarrow \left(midpoint\left(Real, x, y\right) \in intrinsicFrontier\left(Real, base\left(C, u\right)\right) \Leftrightarrow \left(\exists p \in pure\left(C, u\right),\; x \in exclusion\left(C, u, p\right) \land y \in exclusion\left(C, u, p\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ActualExclusionBoundary.original_boundary_cover_and_midpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

V is the original finite dimensional real normed vector space, C the original closed generating pointed cone, and u its actual strictly positive linear unit. The notation base(C,u) means the entire set K of cone points with u equal to one, and pure(C,u) means all extreme points of K. The exclusion D(p) uses all original proper effects f with f(p)=1 and consists of all x in K for which one such f has f(x)=0. No restriction of states or effects is made.

The predicate exclusionBalls requires, for each original pure p, an injective affine parametrization of the entire D(p) by a closed Euclidean unit ball of a positive dimension. Dimensions may vary with p. IntrinsicFrontier is the boundary inside the actual affine span of K. LinearMaps denotes real linear maps, span the real linear span, and top the whole vector space.

At an actual relative boundary point x, membership in the interior of the cone would give membership in the relative interior of its normalized base by restricting to the unit affine hyperplane. Thus x is outside the cone interior. The cone has nonempty interior because it generates V. A geometric Hahn–Banach support functional f therefore attains its maximum on the cone at x. Cone scaling and the zero vector force f(x)=0 and f to be nonpositive on the cone.

The maximizer set of f on the whole K is a convex exposed face containing x. It is proper: if every original pure point maximized f, pure spanning would force f=0. The existing EB face classification makes this face either a whole exclusion or a pure singleton. In the singleton case a pure point of the nonempty compact exclusion of x, together with the symmetry supplied by complementary original effects, places x in a whole exclusion as well.

Each whole exclusion lies in the actual relative boundary. Its common original confirming effect vanishes there but equals one at its confirming pure point. A relative interior point could be extended slightly away from that pure point along the same affine line while remaining in K; linearity would give a negative proper-effect value, which is impossible.

If the midpoint of two points of K is on the boundary, coverage puts that midpoint in one whole exclusion. The extreme-set property forces both endpoints into that same exclusion. Conversely, convexity keeps the midpoint in any common exclusion, hence on the actual boundary. Equal endpoints and the degenerate ambient space remain in scope.

This is the original-boundary midpoint bridge needed for IX116.6. It uses neither Pair properness nor injectivity, orthogonality axioms, common centers or global singleton labels. The following theorem supplies repeated-block isolation, transitivity and the actual compact Hausdorff quotient in the all-repeated contradiction branch. The common rational slice, convex neighborhood controls and radial homotopy obstruction remain further obligations. Existence of a singleton-labelled ball, its propagation and continuum multiplicity are not conclusions here. No originality claim is made.

**Theorem 1.2 (The literal all-repeated boundary quotient).**

$$\forall V \in Types,\; [NormedAddCommGroup\left(V\right)] [NormedSpace\left(Real, V\right)] [FiniteDimensional\left(Real, V\right)] \forall C \in PointedCone\left(Real, V\right),\; \forall u \in LinearMaps\left(Real, V, Real\right),\; \left(OriginalEBDomain\left(C, u\right) \land \left(\forall p \in pure\left(C, u\right),\; \exists s \in pure\left(C, u\right),\; p \ne s \land exclusion\left(C, u, s\right) = exclusion\left(C, u, p\right)\right)\right) \Rightarrow \left(\exists r \in Setoid\left(intrinsicFrontier\left(Real, base\left(C, u\right)\right)\right),\; \left(\forall x \in intrinsicFrontier\left(Real, base\left(C, u\right)\right),\; \forall y \in intrinsicFrontier\left(Real, base\left(C, u\right)\right),\; r\left(x, y\right) \Leftrightarrow midpoint\left(Real, x, y\right) \in intrinsicFrontier\left(Real, base\left(C, u\right)\right)\right) \land \left(\left(\forall x \in intrinsicFrontier\left(Real, base\left(C, u\right)\right),\; \forall y \in intrinsicFrontier\left(Real, base\left(C, u\right)\right),\; r\left(x, y\right) \Leftrightarrow \left(\exists p \in pure\left(C, u\right),\; x \in exclusion\left(C, u, p\right) \land y \in exclusion\left(C, u, p\right)\right)\right) \land \left(IsClosed\left(RelationGraph\left(r\right)\right) \land \left(CompactSpace\left(Quotient\left(r\right)\right) \land \left(TTwoSpace\left(Quotient\left(r\right)\right) \land \left(Continuous\left(QuotientMk\left(r\right)\right) \land \left(Surjective\left(QuotientMk\left(r\right)\right) \land \left(IsClosedMap\left(QuotientMk\left(r\right)\right) \land \left(\forall b \in Quotient\left(r\right),\; \exists p \in pure\left(C, u\right),\; AmbientImage\left(Fiber\left(QuotientMk\left(r\right), b\right)\right) = exclusion\left(C, u, p\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ActualExclusionBoundary.original_all_repeated_boundary_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OriginalEBDomain abbreviates exactly the closedness, strict positivity, generating span and whole positive-dimensional exclusion-ball hypotheses in the preceding statement, with the same V, C and u. The extra assumption says that every original pure label p has a distinct original pure label s with the same entire exclusion set. This is the all-repeated contradiction branch, not an extra assumption on the eventual EB-only existence theorem.

RelationGraph(r) is the set of boundary pairs (x,y) with r(x,y). Setoid means an equivalence relation; QuotientMk is its canonical projection onto its actual quotient. The theorem constructs r as the literal boundary-midpoint predicate and proves that its classes are exactly the whole exclusion blocks through the second displayed equivalence.

To prove isolation, two shared distinct points force two whole exclusion balls to coincide, by applying the existing strict ball-face theorem to their intersection. If a repeated ball meets another different ball, their singleton intersection is pure. The two distinct labels of the repeated ball then force every pure point of that ball to have one common exclusion. Zero symmetry puts all those pure points in the other ball. Compact convex hull generation and maximality force equality, a contradiction. Thus different whole balls are disjoint in this branch, and the midpoint criterion makes the literal relation transitive.

The actual boundary is a closed subset of compact K. The midpoint map is continuous, so its inverse image of that boundary is a closed relation graph. The saturation of a closed boundary subset is the projection of the intersection of this graph with a compact product. It is closed, proving that the actual quotient projection is closed. Its fibers are compact by the same graph argument. The proper-map product theorem then makes the product projection a quotient map; the closed graph descends to the closed diagonal, proving the actual quotient Hausdorff. Compactness descends from the compact actual boundary. For each actual quotient point b, the ambient image of its entire projection fiber equals one whole original exclusion D(p); AmbientImage and Fiber denote precisely that image and inverse image of the singleton b. No convex subset or selected smaller ball replaces the full fiber.

This construction places no ENR, metrizability, finite dimension, fibration or local contractibility hypothesis on the quotient. The common rational Baire slice, ray-avoiding finite-neighborhood data, radial homotopy and sphere contradiction are further obligations. The full original theorem is not settled by construction of this quotient.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/ActualExclusionBoundary.original_all_repeated_boundary_quotient`
- Truth anchor: `D5/S3/Quantum/Foundation/ActualExclusionBoundary.original_boundary_cover_and_midpoint`
- Dependency: [D5/S3/Quantum/Foundation/ExclusionBallFaces](ExclusionBallFaces.md)

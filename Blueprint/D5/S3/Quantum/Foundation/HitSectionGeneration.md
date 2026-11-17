# Pure generators of original linear sections

## Abstract

Actual pure-pair face incidence preserves the original pure generators of every containing linear section.

The original carrier is a finite dimensional real normed vector space V. C is the original closed convex cone containing zero, and u is the original real linear unit, strictly positive at every nonzero vector of C. K is the entire normalized base and P is its entire extreme-point set, as defined by CircuitBalancedConfirmation. The source domain also requires a nonzero carrier and a pointed generating cone; the proof establishes the result without needing those additional restrictions. Neither the set of pure points nor a minimal face is assumed closed. No finite-pure, ball, L2, NC, SP, ROG or PSD premise is introduced.

**Definition 1.1 (All originally distinguishable pure neighbours).**

Lean statement: `D5/S3/Quantum/Foundation/HitSectionGeneration.neighbors`

*Formalization.* `D5/S3/Quantum/Foundation/HitSectionGeneration.neighbors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each a in V, neighbors(C,u,a) is exactly the intersection of the entire original pure set with FacetZeroGluing.exclusion(C,u,a). Thus b is an original pure point and one original real linear effect f satisfies 0 <= f(c) <= u(c) for every c in C, f(a)=1 and f(b)=0. The two readings belong to the same original effect; there is no supplied zero-face or chosen pure subconfiguration.

**Definition 1.2 (Incidence with every actual pure-pair face).**

Lean statement: `D5/S3/Quantum/Foundation/HitSectionGeneration.Hit`

*Formalization.* `D5/S3/Quantum/Foundation/HitSectionGeneration.Hit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every pair p,q in the complete original pure subtype, p != q implies that neighbors(C,u,a) meets WholePairBallConfirmation.pairBase(C,u,p,q). pairBase is the whole normalized slice of the smallest original cone face containing both points: membership is tested against every native cone face containing p and q. The original strict unit and base_face_lift identify this with the actual minimal convex face of K, without changing the face to its closure.

**Theorem 1.3 (Finite pure generation without a closed pure set).**

$$\forall V \in Type,\; [\mathrm{NormedAddCommGroup}\left(V\right)] [\mathrm{NormedSpace}\left(\mathbb{R}, V\right)] [\mathrm{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \mathrm{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \mathrm{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \left(\mathrm{IsClosed}\left(C\right) \land \left(\forall x \in V,\; \left(x \in C \land x \ne 0\right) \Rightarrow 0 < \mathrm{u}\left(x\right)\right)\right) \Rightarrow \mathrm{base}\left(C, u\right) = \mathrm{convexHull}\left(\mathbb{R}, \mathrm{pure}\left(C, u\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/HitSectionGeneration.base_eq_convexHull_pure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original C,u with C closed and u strictly positive on its nonzero elements, the whole base K equals the ordinary real convex hull of all its extreme points. The convex hull is finite, with no closure operation. The assertion includes an empty base and a singleton base. This theorem is consumed by hit_section_generation on both the principal face and the section cone.

For each x in K the proof constructs the native principal face consisting of all y in C for which t*x-y is in C for some nonnegative real t. It contains x. A native cone face equals C intersect its real linear span by the original face_span_inter; finite dimension and closedness of C therefore make this particular face closed. Its normalized base is compact by base_compact. Krein-Milman is used in its exact pinned form with closure. Choose a point y in the intrinsic interior of the convex hull of the face's extreme points. Positive domination explicitly extends the line from y through the designated x within the same face. The pinned open-segment intrinsic-interior theorem then puts x in the ordinary convex hull. Extreme points of the face base are original extreme points. This supplies finite pure generation without assuming it as a premise.

**Theorem 1.4 (All pure and finite conic generators of a hit section).**

$$\forall V \in Type,\; [\mathrm{NormedAddCommGroup}\left(V\right)] [\mathrm{NormedSpace}\left(\mathbb{R}, V\right)] [\mathrm{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \mathrm{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \mathrm{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall a \in \mathrm{pure}\left(C, u\right),\; \forall S \in \mathrm{Submodule}\left(\mathbb{R}, V\right),\; \left(\left(\mathrm{IsClosed}\left(C\right) \land \left(\forall x \in V,\; \left(x \in C \land x \ne 0\right) \Rightarrow 0 < \mathrm{u}\left(x\right)\right)\right) \land \left(\mathrm{Hit}\left(C, u, a\right) \land \mathrm{neighbors}\left(C, u, a\right) \subseteq S\right)\right) \Rightarrow \left(\mathrm{extremePoints}\left(\mathbb{R}, \mathrm{inter}\left(\mathrm{base}\left(C, u\right), S\right)\right) = \mathrm{inter}\left(\mathrm{pure}\left(C, u\right), S\right) \land \left(\mathrm{inter}\left(\mathrm{base}\left(C, u\right), S\right) = \mathrm{convexHull}\left(\mathbb{R}, \mathrm{inter}\left(\mathrm{pure}\left(C, u\right), S\right)\right) \land \mathrm{inter}\left(C, S\right) = \mathrm{PointedConeHull}\left(\mathbb{R}, \mathrm{inter}\left(\mathrm{pure}\left(C, u\right), S\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/HitSectionGeneration.hit_section_generation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original pure a satisfying Hit and every real linear subspace S containing all original neighbours of a, the extreme points of K intersect S are exactly P intersect S, K intersect S is the ordinary real convex hull of P intersect S, and C intersect S is PointedCone.hull over the reals of P intersect S. PointedCone.hull is the nonnegative-scalar submodule span, equivalently all finite nonnegative sums; it includes zero. Empty sections and singleton bases remain in scope.

If a section extreme x were not an original pure point, the compact normalized principal face of x has two distinct extreme points p,q. They are original pure points. Hit produces an original pure neighbour b in the actual pair face, hence in the principal face and in S. The explicit positive-domination extension gives z in the same principal face with x in the open segment from b to z. Linearity of S puts z in S. Section extremeness forces b=x, contradicting the nonpurity of x. The reverse extreme-point inclusion is restriction to a subset. Apply finite pure generation to C intersect S for the second conclusion. For the third, normalize every nonzero c by the same original positive u(c), then rescale its finite convex decomposition. The zero case is retained separately.

The source is Quantum Origin Binary Normal Differences and Orientation XVII, section 197.2, Theorem 197.3. The first result supplies a mature convex-geometric prerequisite; the new incidence argument connects actual face hitting with preservation of the original section generators. Sections 197.3 and the finite-cone argument following it are source applications, not claimed existing Lean consumers. No classification, reconstruction, physical implementation, literature priority, frozen membership or atom coverage follows merely from these declarations.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/HitSectionGeneration.Hit`
- Truth anchor: `D5/S3/Quantum/Foundation/HitSectionGeneration.base_eq_convexHull_pure`
- Truth anchor: `D5/S3/Quantum/Foundation/HitSectionGeneration.hit_section_generation`
- Truth anchor: `D5/S3/Quantum/Foundation/HitSectionGeneration.neighbors`
- Dependency: [D5/S3/Quantum/Foundation/FacetZeroGluing](FacetZeroGluing.md)
- Dependency: [D5/S3/Quantum/Foundation/WholePairBallConfirmation](WholePairBallConfirmation.md)

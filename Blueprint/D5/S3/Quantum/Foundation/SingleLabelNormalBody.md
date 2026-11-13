# Single-label original normal bodies

## Abstract

Whole original positive annihilator bodies control every antipodal gap and force a native dimension bound at a singleton-label exclusion ball.

V is a finite dimensional real normed space, C is its original closed generating cone, and u is strictly positive on each nonzero cone vector. The normalized base K, all its extreme points P, and the full original interval of effects are retained. Every entire original exclusion D(p) has an injective affine chart of a closed Euclidean ball of positive dimension; the dimensions may vary, and segments are included. Only the chosen original p is required to have a singleton label fiber. No Pair, common dimension, width, projectivity, spectrality or Jordan structure is imposed.

**Definition 1.1 (Original singleton label fiber).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.SingleLabel`

*Formalization.* `D5/S3/Quantum/Foundation/SingleLabelNormalBody.SingleLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Among all original pure states, equality of the entire exclusion set with D(p) forces equality with p.

**Definition 1.2 (Whole normalized positive annihilator body).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.normalBody`

*Formalization.* `D5/S3/Quantum/Foundation/SingleLabelNormalBody.normalBody` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the entire subset of the original continuous dual consisting of b nonnegative on the whole cone, with b(p)=0 and b(c)=1. Finite dimensionality identifies this dual with all original real-linear functionals.

**Definition 1.3 (Actual affine restriction slope).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope`

*Formalization.* `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose the original functional with the linear part of the full ball chart and use the Euclidean Riesz identification. Thus b(a(z))=b(a(0))+inner(slope(b),z) for every chart vector z.

**Definition 1.4 (Whole slope image).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slopeBody`

*Formalization.* `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slopeBody` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image is taken over the entire normalized positive annihilator body, without selecting a finite effect menu or replacing its convex body.

**Theorem 1.5 (Full affine slope formula).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every coordinate vector z, the original functional at a(z) equals its value at a(0) plus the inner product of its slope with z.

**Theorem 1.6 (Entire ball membership).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.chart_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.chart_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every vector of norm at most one maps into the entire original exclusion D(p).

**Theorem 1.7 (Chart directions lie in the unit kernel).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.chart_unit_linear`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.chart_unit_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original unit annihilates the chart's linear direction map on the whole coordinate space, because it is constant one on the affinely spanning closed unit ball.

**Definition 1.8 (Original antipodal all-effect gap).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.gap`

*Formalization.* `D5/S3/Quantum/Foundation/SingleLabelNormalBody.gap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any chart vector n, the gap is the original comparison at a(n),a(-n). Comparison is the infimum over every original proper effect confirming a(n). The theorem restricts n to unit vectors, so both endpoints are original pure states.

**Theorem 1.9 (Local propagation of singleton labels).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.single_label_neighbor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.single_label_neighbor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume only the original closed generating cone, strictly positive unit and entire positive-dimensional exclusion-ball charts. If p has a singleton label fiber, every pure q in D(p) also has a singleton label fiber. If another label shared D(q), two-point ball-face rigidity would collapse all pure boundary points of D(q) to p, contradicting its positive dimension. No global existence or topological premise is used.

**Theorem 1.10 (Global maxima lie on the original exclusion face).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.positive_annihilator_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.positive_annihilator_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonzero positive functional b with b(p)=0 has a strictly positive global maximum at an original pure state in D(p). A compact exposed maximum face supplies a pure maximizer; its normalized functional confirms that maximizer and vanishes at p. Original zero symmetry then places the maximizer in D(p).

**Theorem 1.11 (Global bound by twice the original unit).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.normal_body_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.normal_body_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every member of the entire normalized body, positivity on the whole chart ball bounds its slope norm by one. The global maximum identity transfers the resulting bound of two from D(p) to the entire base and hence gives zero <= b <= 2u on the whole cone.

**Theorem 1.12 (Compactness in the original dual).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.normal_body_compact`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.normal_body_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The whole normalized body is closed in the finite dimensional original dual. Its global bound places it inside the compact interval of all effects for the strictly positive unit 2u. No compactness of the pure-state carrier is assumed.

**Theorem 1.13 (Exact original full-ball slope definition).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_body_original`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_body_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership v in the whole image is equivalent to existence of an original real-linear b positive on C, annihilating p, normalized at a(0), with b(a(z))=1+inner(v,z) for every z of the whole closed unit ball. The full ball has full affine span, so the affine formula uniquely determines the restriction slope.

**Theorem 1.14 (Compact convex whole slope body).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_body_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_body_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full slope map is linear and continuous, so the image of the compact convex original body is compact and convex. Its exact original affine formula and positivity on the whole unit ball give containment in the closed unit ball.

**Theorem 1.15 (Actual positive slope on every unit ray).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.positive_ray`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.positive_ray` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit direction n, the actual boundary state q=a(n) has a singleton label by local propagation. A common original confirmer of q vanishing on all of D(q) has restriction 1-lambda+lambda inner(n,z) on D(p), with zero < lambda <= 1/2. A zero lambda would make all pure states of D(p) share D(q). Normalizing this actual confirmer at a(0) gives a member of the entire original body with slope t n, where zero < t <= 1.

**Theorem 1.16 (Finite directional selection gives a uniform inner ball).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_body_inradius`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_body_inradius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose an actual positive ray point for each of the finitely many signed coordinate directions. Their positive minimum eta and convexity give all signed eta-axis points. Averaging d coordinate points proves containment of the Euclidean ball of radius eta/d, which is positive and at most one. This sufficient radius need not be optimal; the body remains the whole image.

**Theorem 1.17 (Exact zero gap locus).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.zero_gap_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.zero_gap_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original unit direction, the original all-effect gap vanishes exactly when that unit direction belongs to the whole slope body. A unit slope yields the legal original confirming effect b/2. Conversely compactness of the entire confirming-effect fiber gives an attained zero, hence the antipode belongs to D(q). A common original confirmer vanishes there and at p, and doubling it realizes the exact unit slope. This equivalence does not require the singleton-label hypothesis.

**Theorem 1.18 (Uniform bound over all original unit directions).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.uniform_original_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.uniform_original_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each fixed singleton-label p and every full chart, one radius zero < rho <= 1 satisfies rho-ball containment. For every unit n the original gap is at most (1-rho)/(1+rho), which is strictly below one, and its zero locus is exactly membership of n in the whole slope body. A positive annihilator of slope rho n has global maximum 1+rho, so dividing by that value gives a legal effect in the entire original interval.

**Theorem 1.19 (Dimension bound in the original carrier).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.native_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.native_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original pure q in D(p) and its entire chart, dim(V) >= d(p)+d(q)+1. Positivity makes every functional annihilating p vanish on the actual d(q)-1 tangent directions of D(q) at p. These directions lie in ker(u), whereas u(p)=1. The inner slope ball separates the constant and all d(p) directions of D(p). Their direct sum with p and the actual tangent space injects into V, giving the bound by finite dimensional linear algebra.

Actual triangle application. Keep the same entire normalized base K=C∩{u=1}, all its extreme points P, the entire interval of original effects, and the original mixed-state exclusion D(p). Assume that every exclusion is a whole affine three-ball and that p↦D(p) is injective. Fix any three original pure vertices p0,p1,p2 with three independently witnessed original orthogonal edges. Exclusion symmetry gives both orientations, and the confirming readings force the vertices to be distinct. The first part of ExclusionBallFaces.exclusion_ball_faces supplies common original confirmers; choose any ai confirming pi and vanishing on all of D(pi). OriginalWidthContact.top_subsingleton_of_zero_exclusion shows that the one-value face of each chosen ai, including mixed states, is exactly {pi}. No singleton-confirmer seed or whole-pair premise is used.

For each i, use any entire three-ball chart Ai(z)=ci+Bi(z) of D(pi). With j=i+1 and k=i+2 modulo three, the opposite vertices have actual chart coordinates ni and -ni with norm(ni)=1. WholePairBallConfirmation.affine_zero_antipode and the original effect bounds give ci=(pj+pk)/2, Bi(ni)=(pj-pk)/2, aj(Ai(z))=(1+inner(ni,z))/2 and ak(Ai(z))=(1-inner(ni,z))/2 for every chart vector z. These identities refer to the supplied chart itself. Its linear range Wi is span{x-ci:x∈D(pi)} and has dimension three. Transport its own Euclidean inner product through the injective Bi. Then Li=Bi((R ni)⊥) is precisely the orthogonal transverse plane to the actual diameter, and has dimension two; different Wi need no common inner product.

Put Mi=span D(pi) and U=M0+M1+M2. For each i the map (alpha,beta,z)↦alpha pj+beta pk+Bi(z), with z∈(R ni)⊥, is injective and has range Mi. Thus Mi=R pj⊕R pk⊕Li, ai vanishes on Mi, and Li=Mi∩ker(aj)∩ker(ak). Indeed z decomposes as inner(ni,z) ni plus its perpendicular remainder, and the two displayed effect formulas recover the two scalar coefficients. This is an internal decomposition of each actual Mi; the three Mi are summed to define U.

For every original positive functional h with h(pi)=0, SingleLabelNormalBody.tangent_annihilation makes h vanish on Lj for j≠i. Its restriction to Mj is h(pk) times the restriction of ak, by the same whole-ball antipodal formula and linear spanning. For its own chart, injectivity of the exclusion map gives SingleLabel at pi; SingleLabelNormalBody.positive_ray supplies an actual positive annihilator with positive slope in each normalized nonzero direction. The slope formula then separates every nonzero vector of Li. Consequently F(alpha,z)=Σi alpha_i pi+Σi Bi(zi), for alpha∈R^3 and zi∈(R ni)⊥, is injective and has range U. Applying the chosen ai first kills all alpha_i in a kernel relation; applying all positive annihilators at pi then kills zi. Its domain has dimension 3+2+2+2=9, so U=R p0⊕R p1⊕R p2⊕L0⊕L1⊕L2 and dim U=9.

The actual barycenter eta=(p0+p1+p2)/3 belongs to intrinsicInterior(R,K). If eta belonged to D(s), a common original confirmer at s would vanish on all three vertices by positivity. The original exclusions D(s) and D(p0) would then share the two distinct vertices p1,p2. SingleLabelNormalBody.equal_of_two_points forces their equality, contradicting p0∉D(p0). MixedExclusionGeometry.frontier_covered rules out every point of the original intrinsic frontier in this way. The base-to-cone inclusion intrinsicInterior(R,K)⊆interior(C) also holds in the original ambient space: a supporting functional at a point outside interior(C), normalized by ExclusionBallFaces.positive_support_confirmer, puts that point in an original exclusion; MixedExclusionGeometry.exclusion_frontier then contradicts relative interior. Hence the same eta is in interior(C), without restricting either interior claim to U.

The chosen effects satisfy Σi ai(x)=u(x) for every x∈U. On the three original vertices their readings are the Kronecker delta, and every ai vanishes on every transverse plane; u vanishes on all chart directions by SingleLabelNormalBody.chart_unit_linear. These restrictions determine the equality on the six displayed blocks. They assert no equality on the rest of V, no identification U=V or dim V=9, and no common physical three-outcome instrument. The triangle calculation is an application of the cited original-domain results and finite dimensional linear algebra, with no literature-priority or physical-realization claim.

The local theorem fixes a singleton-label p and proves neighbor propagation without importing a global existence theorem. In the case where every full ball has dimension three, its dimension inequality gives seven once such a p exists. Unconditional existence from EB alone requires the separate global topological theorem; that theorem is not supplied here. A positive inner radius does not assert that the body equals the unit ball or that every antipodal gap vanishes. These are mathematical statements about the specified original model, without a physical realization or literature-priority claim.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.SingleLabel`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.chart_mem`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.chart_unit_linear`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.gap`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.native_dimension`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.normalBody`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.normal_body_bound`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.normal_body_compact`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.positive_annihilator_maximum`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.positive_ray`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.single_label_neighbor`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slopeBody`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_body_geometry`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_body_inradius`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_body_original`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_formula`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.uniform_original_gap`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.zero_gap_iff`
- Dependency: [D5/S3/Quantum/Foundation/ContinuousFrameSum](ContinuousFrameSum.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalFacePolarity](OriginalFacePolarity.md)

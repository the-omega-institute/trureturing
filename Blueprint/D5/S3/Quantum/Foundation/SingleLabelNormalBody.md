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

**Definition 1.5 (Original antipodal all-effect gap).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.gap`

*Formalization.* `D5/S3/Quantum/Foundation/SingleLabelNormalBody.gap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any chart vector n, the gap is the original comparison at a(n),a(-n). Comparison is the infimum over every original proper effect confirming a(n). The theorem restricts n to unit vectors, so both endpoints are original pure states.

**Theorem 1.6 (Local propagation of singleton labels).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.single_label_neighbor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.single_label_neighbor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume only the original closed generating cone, strictly positive unit and entire positive-dimensional exclusion-ball charts. If p has a singleton label fiber, every pure q in D(p) also has a singleton label fiber. If another label shared D(q), two-point ball-face rigidity would collapse all pure boundary points of D(q) to p, contradicting its positive dimension. No global existence or topological premise is used.

**Theorem 1.7 (Global maxima lie on the original exclusion face).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.positive_annihilator_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.positive_annihilator_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonzero positive functional b with b(p)=0 has a strictly positive global maximum at an original pure state in D(p). A compact exposed maximum face supplies a pure maximizer; its normalized functional confirms that maximizer and vanishes at p. Original zero symmetry then places the maximizer in D(p).

**Theorem 1.8 (Global bound by twice the original unit).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.normal_body_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.normal_body_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every member of the entire normalized body, positivity on the whole chart ball bounds its slope norm by one. The global maximum identity transfers the resulting bound of two from D(p) to the entire base and hence gives zero <= b <= 2u on the whole cone.

**Theorem 1.9 (Compactness in the original dual).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.normal_body_compact`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.normal_body_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The whole normalized body is closed in the finite dimensional original dual. Its global bound places it inside the compact interval of all effects for the strictly positive unit 2u. No compactness of the pure-state carrier is assumed.

**Theorem 1.10 (Exact original full-ball slope definition).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_body_original`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_body_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership v in the whole image is equivalent to existence of an original real-linear b positive on C, annihilating p, normalized at a(0), with b(a(z))=1+inner(v,z) for every z of the whole closed unit ball. The full ball has full affine span, so the affine formula uniquely determines the restriction slope.

**Theorem 1.11 (Compact convex whole slope body).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_body_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_body_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full slope map is linear and continuous, so the image of the compact convex original body is compact and convex. Its exact original affine formula and positivity on the whole unit ball give containment in the closed unit ball.

**Theorem 1.12 (Actual positive slope on every unit ray).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.positive_ray`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.positive_ray` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit direction n, the actual boundary state q=a(n) has a singleton label by local propagation. A common original confirmer of q vanishing on all of D(q) has restriction 1-lambda+lambda inner(n,z) on D(p), with zero < lambda <= 1/2. A zero lambda would make all pure states of D(p) share D(q). Normalizing this actual confirmer at a(0) gives a member of the entire original body with slope t n, where zero < t <= 1.

**Theorem 1.13 (Finite directional selection gives a uniform inner ball).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_body_inradius`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.slope_body_inradius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose an actual positive ray point for each of the finitely many signed coordinate directions. Their positive minimum eta and convexity give all signed eta-axis points. Averaging d coordinate points proves containment of the Euclidean ball of radius eta/d, which is positive and at most one. This sufficient radius need not be optimal; the body remains the whole image.

**Theorem 1.14 (Exact zero gap locus).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.zero_gap_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.zero_gap_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original unit direction, the original all-effect gap vanishes exactly when that unit direction belongs to the whole slope body. A unit slope yields the legal original confirming effect b/2. Conversely compactness of the entire confirming-effect fiber gives an attained zero, hence the antipode belongs to D(q). A common original confirmer vanishes there and at p, and doubling it realizes the exact unit slope. This equivalence does not require the singleton-label hypothesis.

**Theorem 1.15 (Uniform bound over all original unit directions).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.uniform_original_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.uniform_original_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each fixed singleton-label p and every full chart, one radius zero < rho <= 1 satisfies rho-ball containment. For every unit n the original gap is at most (1-rho)/(1+rho), which is strictly below one, and its zero locus is exactly membership of n in the whole slope body. A positive annihilator of slope rho n has global maximum 1+rho, so dividing by that value gives a legal effect in the entire original interval.

**Theorem 1.16 (Dimension bound in the original carrier).**

Lean statement: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.native_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/SingleLabelNormalBody.native_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original pure q in D(p) and its entire chart, dim(V) >= d(p)+d(q)+1. Positivity makes every functional annihilating p vanish on the actual d(q)-1 tangent directions of D(q) at p. These directions lie in ker(u), whereas u(p)=1. The inner slope ball separates the constant and all d(p) directions of D(p). Their direct sum with p and the actual tangent space injects into V, giving the bound by finite dimensional linear algebra.

The local theorem fixes a singleton-label p and proves neighbor propagation without importing a global existence theorem. In the case where every full ball has dimension three, its dimension inequality gives seven once such a p exists. Unconditional existence from EB alone requires the separate global topological theorem; that theorem is not supplied here. A positive inner radius does not assert that the body equals the unit ball or that every antipodal gap vanishes. These are mathematical statements about the specified original model, without a physical realization or literature-priority claim.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.SingleLabel`
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
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.uniform_original_gap`
- Truth anchor: `D5/S3/Quantum/Foundation/SingleLabelNormalBody.zero_gap_iff`
- Dependency: [D5/S3/Quantum/Foundation/ContinuousFrameSum](ContinuousFrameSum.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalFacePolarity](OriginalFacePolarity.md)

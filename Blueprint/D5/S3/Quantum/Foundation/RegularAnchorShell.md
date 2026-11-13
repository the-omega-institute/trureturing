# Actual regular-anchor shell

## Abstract

The closure of the actual regular-anchor ratio image has exact support, an attained sphere minimum and inner-ball contact.

Keep the same finite dimensional real carrier V, original cone C, unit u, entire base K, pure anchor p, actual common effect e and full three-ball chart a. NativeChart is the derived interface of RegularAnchorNormalChart.regular_anchor_native, obtained from the original closedness, strict positivity, generation, EB3, exclusion injectivity and regularity hypotheses. Every result below applies to that very interface. The ratio image and rho are those of RegularAnchorWidthAntipode; neither is replaced by a model or a restricted state family.

**Definition 1.1 (Closed actual shell).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorShell.shell`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorShell.shell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

S is the closure of the image of every state x in K other than p under H(x)/g(x), with g=u-e. The actual image need not be closed.

**Theorem 1.2 (Convexity of the entire actual image).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorShell.actual_image_convex`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorShell.actual_image_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two original states x,y and nonnegative weights s,t summing to one, normalize s*x/g(x)+t*y/g(y) by d=s/g(x)+t/g(y). Both gaps are strictly positive, hence d is positive. The resulting original base state has gap 1/d and its actual ratio is the requested convex combination. It cannot be the anchor. Closure preserves convexity; the existing whole-image norm bound makes S compact. The entire actual unit ball lies in S, giving nonempty ambient interior.

**Theorem 1.3 (Exact shell support relation).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorShell.shell_support_le_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorShell.shell_support_le_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real bound r and every vector v, all z in S satisfy -inner(v,z)<=r exactly when rho(v)<=r. Continuous linear evaluation extends the upper bound from the entire actual image to its closure. Thus the ordinary support of S at -v is precisely the original rho(v).

**Theorem 1.4 (Global directional Lipschitz bound).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorShell.rho_lipschitz`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorShell.rho_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite positive M bounds every ratio vector. Cauchy-Schwarz bounds each change of support reading by M times norm(v-w). Taking the bounded real supremum in both directions gives the absolute difference estimate for all vectors v,w, and therefore continuity on the whole coordinate space.

**Definition 1.5 (Entire sphere minimum).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorShell.minimum`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorShell.minimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real infimum is taken over rho evaluated on the entire unit sphere of the actual three-dimensional coordinate space.

**Theorem 1.6 (Attainment and inner-ball lower bound).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorShell.minimum_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorShell.minimum_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity on the nonempty compact sphere supplies an actual unit minimizing direction. Its value equals the defined infimum and is at least one; every other unit direction has value at least this same minimum. The infimum is therefore the source minimum, with no assumed attainment field.

**Theorem 1.7 (Actual contact point identifies the direction).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorShell.ball_frontier_direction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorShell.ball_frontier_direction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If z lies both in the closed inner ball and on the boundary of S, then norm(z)=1 and rho(-z)=1. A supporting functional exists because S is convex with nonempty interior. Riesz representation and normalization give its unit normal b. Inner-ball containment yields 1<=inner(b,z)<=norm(z)<=1; equality forces b=z. The direction in rho is exactly -z.

**Theorem 1.8 (Unit support gives the actual point -v).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorShell.rho_one_frontier`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorShell.rho_one_frontier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For unit v with rho(v)=1, the actual image already contains -v, supplied by the original chart state a(-v). This point belongs to S and saturates its supporting inequality. Any interior neighborhood would contain a slightly farther point in direction -v, contradicting that inequality. Hence -v belongs to the shell boundary.

**Theorem 1.9 (Exact sphere-minimum and ball-boundary equivalence).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorShell.minimum_one_iff_contact`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorShell.minimum_one_iff_contact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The minimum equals one exactly when the closed original coordinate unit ball meets the boundary of its actual shell. An attaining unit direction supplies the contact point -v. Conversely an actual contact z supplies the unit direction -z with rho(-z)=1, while the minimum is at least one. No smoothness, strict convexity or closedness of the actual ratio image is assumed.

**Theorem 1.10 (All unit support halfspaces reconstruct the actual shell).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorShell.mem_shell_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorShell.mem_shell_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A vector z belongs to S exactly when -inner(v,z)<=rho(v) for every unit v. For a point outside the actual closed convex S, strict separation supplies a real continuous functional. Its nonzero Riesz vector gives a unit direction contradicting the asserted inequality. This reconstruction is proved for the actual shell rather than supplied as a bridge premise.

**Theorem 1.11 (Containment at the minimum support radius).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorShell.minimum_ball_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorShell.minimum_ball_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entire closed ball of radius delta=minimum(rho) lies in S. For every unit support direction, Cauchy-Schwarz bounds the reading of a vector in this ball by delta, which is no greater than its actual directional support. The proved halfspace reconstruction gives containment. Since delta>=1, this closed ball is exactly delta times the closed unit ball.

**Theorem 1.12 (Strict containment and every boundary distance).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorShell.strict_margin`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorShell.strict_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If delta>1, the entire original closed unit ball lies in the ambient interior of S. Every boundary point has norm at least delta, since the open ball of radius delta lies in the shell interior. The triangle inequality then gives dist(x,y)>=delta-1 for every inner-ball x and every boundary y.

**Definition 1.13 (Distance of the whole ball from the whole boundary).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorShell.boundaryDistance`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorShell.boundaryDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set distance is the real infimum of all distances dist(x,y), with x in the entire closed unit ball and y on the entire boundary of S. Both sets are nonempty: S contains the unit ball and is a bounded proper convex body, so its boundary is nonempty.

**Theorem 1.14 (Positive distance from the actual boundary).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorShell.strict_boundary_distance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorShell.strict_boundary_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For delta>1, the set distance is at least delta-1, and delta-1 is strictly positive. Nonemptiness of the distance-value set gives the ordinary real-infimum lower bound; the estimate covers every pair of actual points in the specified sets.

The width equivalence uses RegularAnchorWidthAntipode.width_one_iff_rho_one together with the attained full-sphere minimum. These geometric results preserve the actual chart signs and original state and effect domains. They do not assert a physical realization or a literature novelty claim.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorShell.actual_image_convex`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorShell.ball_frontier_direction`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorShell.boundaryDistance`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorShell.mem_shell_iff`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorShell.minimum`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorShell.minimum_attained`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorShell.minimum_ball_subset`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorShell.minimum_one_iff_contact`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorShell.rho_lipschitz`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorShell.rho_one_frontier`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorShell.shell`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorShell.shell_support_le_iff`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorShell.strict_boundary_distance`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorShell.strict_margin`
- Dependency: [D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode](RegularAnchorWidthAntipode.md)

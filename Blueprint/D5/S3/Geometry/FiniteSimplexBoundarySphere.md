# Finite simplex boundary sphere

## Abstract

Rational Psi on the literal finite simplex, its full-boundary quotient, the Euclidean unit sphere and the original supported coordinate realization.

This construction starts from the existing finite-product coordinate simplex. Its explicit L2 transport supports the rational sphere map. Both quotients identify the entire boundary, and the ambient bridge retains the original face labels and zero ghost coordinates.

**Definition 1.1 (Literal Euclidean simplex).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.Simplex`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.Simplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinates are nonnegative and sum to one in EuclideanSpace ℝ Λ. The norm used in every sphere calculation is the Euclidean L2 norm.

**Definition 1.2 (Full face boundary).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.boundary`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.boundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A boundary witness is a label of Λ at which the coordinate vanishes. A label outside an ambient face is never such a witness.

**Definition 1.3 (Full-boundary relation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.boundaryRelation`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.boundaryRelation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two representatives are related exactly when they are equal or both belong to the full boundary.

**Definition 1.4 (Literal collapse relation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.boundarySetoid`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.boundarySetoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Equality-or-both-boundary is reflexive, symmetric and transitive; BoundaryQuotient is its native Setoid quotient.

**Definition 1.5 (Finite-product topology bridge).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.coordinateBridge`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.coordinateBridge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

WithLp.toLp 2 and WithLp.ofLp restrict to inverse maps between the existing faceSimplex univ and Simplex. Their continuity transports the finite-product topology without equating its function norm with the L2 norm.

**Definition 1.6 (Uniform barycenter).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.barycenter`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.barycenter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Writing m=card(Λ), every barycenter coordinate is 1/m. For nonempty Λ these coordinates are positive and sum to one.

**Definition 1.7 (Normalized pole).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.pole`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.pole` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every pole coordinate is 1/sqrt(m). Its squared L2 norm is m/m=1. A vector of coordinate sum zero is orthogonal to this pole.

**Definition 1.8 (Barycenter representative).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.barycenterPoint`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.barycenterPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The uniform barycenter equipped with its nonnegative and sum-one data is an actual simplex point.

**Definition 1.9 (Rational sphere formula).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiRaw`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiRaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Put z=x−b, sigma=m min_i x_i, a=‖z‖₂² and D=sigma²+a. The formula is D⁻¹(2 sigma z+(sigma²−a)c), with b the barycenter and c the pole. Every minimum ranges over Λ.

**Definition 1.10 (Rational denominator).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiDenominator`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiDenominator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical denominator is sigma squared plus the squared L2 norm of displacement from the barycenter. Its public lower-bound theorem applies to this same term.

**Theorem 1.11 (Uniform denominator estimate).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiDenominator_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiDenominator_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a minimum label j, m z_j=sigma−1 and z_j²≤‖z‖₂². With r=1−sigma this gives D≥(1−r)²+r²/m². Equivalently, D−1/(m²+1) is the sum of ((m²+1)sigma−1)²/(m²(m²+1)) and a−(sigma−1)²/m², both nonnegative.

**Theorem 1.12 (Actual L2 sphere equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiRaw_norm_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiRaw_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The norm-of-sum expansion has zero cross term because z is orthogonal to c. Its numerator square is 4 sigma² a+(sigma²−a)²=D², so division by the positive denominator gives norm square one.

**Definition 1.13 (North pole in the metric sphere).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.north`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.north` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalized constant pole, with its actual metric-sphere membership.

**Definition 1.14 (South pole in the metric sphere).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.south`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.south` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The negative of the normalized pole, in the same Euclidean sphere.

**Definition 1.15 (Sphere-valued rational map).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational vector formula is equipped with its norm-one proof; the target is the repository EuclideanSphereJoin.UnitSphere.

**Theorem 1.16 (Continuity at every representative).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.continuous_psiRaw`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.continuous_psiRaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite coordinate minima, displacement and the squared L2 norm are continuous. The denominator has a positive lower bound already for every nonempty label type; reciprocal continuity therefore applies at the barycenter and every boundary point.

**Theorem 1.17 (Exact full-boundary image).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A vanishing face coordinate is equivalent to sigma=0. The denominator then equals the positive displacement square, and Psi is south.

**Theorem 1.18 (Exact south fiber).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_south_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_south_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pole component minus one forces sigma=0. The attained minimum identifies this with the full boundary, giving the converse as well.

**Theorem 1.19 (Exact fibers and scale recovery).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Away from south, the pole and tangential components together recover w=(y−alpha c)/(1+alpha)=z/sigma. The finite minimum then supplies sigma(1+m max_i(−w_i))=1, recovering sigma and x=b+sigma w. The pole component alone does not recover sigma. Boundary representatives all have south image.

**Definition 1.20 (Explicit inverse away from south).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.nonSouthInverse`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.nonSouthInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For unit y≠−c let alpha=inner(y,c), v=y−alpha c, M=max_i(−v_i) and kappa=1+alpha+m M. The vector v has sum zero and square norm 1−alpha². Thus M≥0, alpha>−1 and kappa>0. The inverse representative is x=b+v/kappa.

**Theorem 1.21 (Exact inverse substitution).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_nonSouthInverse`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_nonSouthInverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse has min x=(1+alpha)/(m kappa), sigma=(1+alpha)/kappa, z=v/kappa and D=2(1+alpha)/kappa². Substitution makes the tangential coefficient one and the pole coefficient alpha, hence Psi x=v+alpha c=y. This also covers north.

**Theorem 1.22 (Surjection onto the full sphere).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit inverse supplies every non-south point. For south choose a vertex and a different coordinate label; card(Λ)≥2 supplies that label and its coordinate is zero.

**Definition 1.23 (Native quotient descent).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiQuotientMap`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiQuotientMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact equality-or-full-boundary fiber relation makes Quotient.lift well defined, with its literal beta equation and native quotient continuity.

**Definition 1.24 (Full-boundary quotient homeomorphism).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing faceSimplex equals the convex hull of its finite set of coordinate vertices and is compact. The coordinate bridge transports compactness to Simplex, and the quotient is compact. Exact fibers and surjectivity give a continuous bijection to the Hausdorff Euclidean sphere; compact-to-Hausdorff supplies inverse continuity including at south.

**Definition 1.25 (Norm-preserving sphere reindexing).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.reindexSphere`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.reindexSphere` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An equivalence Λ≃Fin((card Λ−1)+1) induces a LinearIsometryEquiv.piLpCongrLeft. Its norm_map and the inverse norm_map justify the sphere restrictions, giving the existing StdSphere(card Λ−1).

**Definition 1.26 (Chosen standard index equivalence).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.stdIndex`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.stdIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact chosen equivalence is equivFin followed by finCongr for card Λ=(card Λ−1)+1, under card Λ≥2.

**Definition 1.27 (Composed StdSphere endpoint).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryStdSphere`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryStdSphere` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose the literal full-boundary quotient homeomorphism with the actual isometric reindexing to StdSphere(card Λ−1).

**Definition 1.28 (Original face labels).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.FaceIndex`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.FaceIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FaceIndex G face is the subtype of original ground labels belonging to face. All minima and maxima continue to range over this subtype.

**Definition 1.29 (Zero extension into the original ground).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A face vector retains its value at each original face label and has zero coordinate at every original off-face label.

**Theorem 1.30 (Ghost evaluation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_apply_ghost`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_apply_ghost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a label outside face, zero extension evaluates to zero. Such a label contributes no minimum, maximum or boundary witness.

**Definition 1.31 (Zero-extension and restriction homeomorphism).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceCoordinateHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceCoordinateHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map from the face-label simplex to the original ambient faceSimplex is zero extension. Its inverse restricts at each original face label. The two coordinate equations prove both inverse laws, and coordinate projections prove continuity in both directions.

**Definition 1.32 (Full boundary of the ambient face).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceBoundary`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An ambient face point is in the face boundary when some ground label belonging to face has zero coordinate. Off-face zeros are excluded.

**Theorem 1.33 (Boundary compatibility).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceCoordinateHomeomorph_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceCoordinateHomeomorph_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero extension preserves and reflects the boundary condition over face labels, with the original ground-label witnesses retained.

**Definition 1.34 (Ambient full-boundary relation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceBoundarySetoid`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceBoundarySetoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original ambient face quotient identifies exactly equal representatives or two points on this face boundary.

**Definition 1.35 (Original ambient quotient homeomorphism).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict an original ambient representative to its face coordinates, apply Psi, and descend through the literal ambient face-boundary relation. The finite convex hull supplies compactness and the same exact-fiber argument gives the homeomorphism to the face-indexed Euclidean sphere.

**Definition 1.36 (Real cardinality).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.cardR`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.cardR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real number obtained by casting the finite face-label cardinality; this is shared by the rational sphere formula and the actual disk collar.

**Theorem 1.37 (Positive nonempty cardinality).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.cardR_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.cardR_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty finite label type, its real cardinality is positive.

**Theorem 1.38 (Nonzero nonempty cardinality).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.cardR_ne`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.cardR_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty finite label type, its real cardinality is nonzero.

**Definition 1.39 (Face-coordinate minimum).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite attained minimum of the actual simplex coordinates over its own label type; it never includes ambient ghosts outside a face.

**Definition 1.40 (The shared barycentric gauge).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the face-coordinate minimum by the real face-label cardinality.

**Theorem 1.41 (An actual minimum label).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every literal finite nonempty simplex point has a label whose coordinate equals the minimum.

**Theorem 1.42 (Minimum below every coordinate).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord_le`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every original simplex label the attained minimum is at most that coordinate.

**Theorem 1.43 (Nonnegative barycentric gauge).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common sigma gauge is nonnegative for every literal simplex point.

**Theorem 1.44 (Full-boundary gauge equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty simplex, sigma is zero exactly when some face-label coordinate is zero; the minimum is attained.

**Theorem 1.45 (Continuous face-coordinate minimum).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.continuous_minCoord`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.continuous_minCoord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite coordinate minimum is continuous in the actual L2 simplex topology.

**Definition 1.46 (A literal coordinate vertex).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.vertex`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual simplex point with coordinate one at the selected label and zero at every other label.

**Theorem 1.47 (A real boundary point when at least two labels exist).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.vertex_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.vertex_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For cardinality at least two, any literal coordinate vertex has a distinct face label of coordinate zero and hence belongs to the full boundary.

The rational map, exact fiber criterion and non-south inverse require only a nonempty finite label type. Surjectivity and the reusable full-sphere quotient homeomorphism assume card(Λ)≥2. For card(Λ)=1 the standalone simplex quotient is a single point. The extra collapsed component needed for an attached-space S0 consumer, the disk collar, the literal attachment map and the universal graph supplier remain separate mathematical obligations.

## References

- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.FaceIndex`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.Simplex`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.barycenter`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.barycenterPoint`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.boundary`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.boundaryRelation`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.boundarySetoid`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.cardR`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.cardR_ne`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.cardR_pos`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.continuous_minCoord`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.continuous_psiRaw`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.coordinateBridge`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceBoundary`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceBoundarySetoid`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceCoordinateHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceCoordinateHomeomorph_boundary`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord_attained`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord_le`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.nonSouthInverse`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.north`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.pole`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiDenominator`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiDenominator_lower_bound`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiQuotientMap`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiRaw`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiRaw_norm_sq`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_boundary`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_eq_iff`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_nonSouthInverse`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_south_iff`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_surjective`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.reindexSphere`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma_eq_zero_iff`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma_nonneg`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryStdSphere`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.south`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.stdIndex`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.vertex`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.vertex_boundary`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_apply_ghost`
- Dependency: [D5/S3/Geometry/EuclideanSphereJoin](EuclideanSphereJoin.md)
- Dependency: [D5/S3/Geometry/FiniteConeCollapse](FiniteConeCollapse.md)

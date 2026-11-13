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

**Theorem 1.10 (Uniform denominator estimate).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiDenominator_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiDenominator_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a minimum label j, m z_j=sigma−1 and z_j²≤‖z‖₂². With r=1−sigma this gives D≥(1−r)²+r²/m². Equivalently, D−1/(m²+1) is the sum of ((m²+1)sigma−1)²/(m²(m²+1)) and a−(sigma−1)²/m², both nonnegative.

**Theorem 1.11 (Actual L2 sphere equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiRaw_norm_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiRaw_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The norm-of-sum expansion has zero cross term because z is orthogonal to c. Its numerator square is 4 sigma² a+(sigma²−a)²=D², so division by the positive denominator gives norm square one.

**Definition 1.12 (North pole in the metric sphere).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.north`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.north` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalized constant pole, with its actual metric-sphere membership.

**Definition 1.13 (South pole in the metric sphere).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.south`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.south` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The negative of the normalized pole, in the same Euclidean sphere.

**Definition 1.14 (Sphere-valued rational map).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational vector formula is equipped with its norm-one proof; the target is the repository EuclideanSphereJoin.UnitSphere.

**Theorem 1.15 (Continuity at every representative).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.continuous_psiRaw`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.continuous_psiRaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite coordinate minima, displacement and the squared L2 norm are continuous. The denominator has a positive lower bound already for every nonempty label type; reciprocal continuity therefore applies at the barycenter and every boundary point.

**Theorem 1.16 (Exact barycenter image).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_barycenter`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_barycenter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At b the displacement is zero and sigma is one, so Psi sends this literal representative to north.

**Theorem 1.17 (Exact full-boundary image).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A vanishing face coordinate is equivalent to sigma=0. The denominator then equals the positive displacement square, and Psi is south.

**Theorem 1.18 (Exact north fiber).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_north_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_north_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pole component is (sigma²−a)/D. If it equals one, a is zero and the representative is b. Conversely the barycenter has north image.

**Theorem 1.19 (Exact south fiber).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_south_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_south_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pole component minus one forces sigma=0. The attained minimum identifies this with the full boundary, giving the converse as well.

**Theorem 1.20 (Exact fibers and scale recovery).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Away from south, the pole and tangential components together recover w=(y−alpha c)/(1+alpha)=z/sigma. The finite minimum then supplies sigma(1+m max_i(−w_i))=1, recovering sigma and x=b+sigma w. The pole component alone does not recover sigma. Boundary representatives all have south image.

**Definition 1.21 (Explicit inverse away from south).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.nonSouthInverse`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.nonSouthInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For unit y≠−c let alpha=inner(y,c), v=y−alpha c, M=max_i(−v_i) and kappa=1+alpha+m M. The vector v has sum zero and square norm 1−alpha². Thus M≥0, alpha>−1 and kappa>0. The inverse representative is x=b+v/kappa.

**Theorem 1.22 (Exact inverse substitution).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_nonSouthInverse`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_nonSouthInverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse has min x=(1+alpha)/(m kappa), sigma=(1+alpha)/kappa, z=v/kappa and D=2(1+alpha)/kappa². Substitution makes the tangential coefficient one and the pole coefficient alpha, hence Psi x=v+alpha c=y. This also covers north.

**Theorem 1.23 (Public inverse coordinate equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.nonSouthInverse_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.nonSouthInverse_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every inverse coordinate is 1/m plus the corresponding tangential coordinate divided by kappa. The maximum in kappa ranges over the original face labels.

**Theorem 1.24 (Surjection onto the full sphere).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit inverse supplies every non-south point. For south choose a vertex and a different coordinate label; card(Λ)≥2 supplies that label and its coordinate is zero.

**Definition 1.25 (Native quotient descent).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiQuotientMap`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiQuotientMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact equality-or-full-boundary fiber relation makes Quotient.lift well defined, with its literal beta equation and native quotient continuity.

**Definition 1.26 (Full-boundary quotient homeomorphism).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing faceSimplex equals the convex hull of its finite set of coordinate vertices and is compact. The coordinate bridge transports compactness to Simplex, and the quotient is compact. Exact fibers and surjectivity give a continuous bijection to the Hausdorff Euclidean sphere; compact-to-Hausdorff supplies inverse continuity including at south.

**Theorem 1.27 (Arbitrary representative equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph_representative`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x, the quotient homeomorphism applied to Quotient.mk x is exactly psi x. This retains the map needed by a later literal attachment quotient.

**Theorem 1.28 (Quotient barycenter equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph_barycenter`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph_barycenter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The class of the literal barycenter is sent exactly to north.

**Theorem 1.29 (Quotient boundary equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The class of any full-boundary point is sent exactly to south.

**Definition 1.30 (Norm-preserving sphere reindexing).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.reindexSphere`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.reindexSphere` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An equivalence Λ≃Fin((card Λ−1)+1) induces a LinearIsometryEquiv.piLpCongrLeft. Its norm_map and the inverse norm_map justify the sphere restrictions, giving the existing StdSphere(card Λ−1).

**Definition 1.31 (Chosen standard index equivalence).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.stdIndex`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.stdIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact chosen equivalence is equivFin followed by finCongr for card Λ=(card Λ−1)+1, under card Λ≥2.

**Definition 1.32 (Composed StdSphere endpoint).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryStdSphere`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryStdSphere` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose the literal full-boundary quotient homeomorphism with the actual isometric reindexing to StdSphere(card Λ−1).

**Theorem 1.33 (Standard-sphere representative equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryStdSphere_representative`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryStdSphere_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every quotient representative maps to the actual isometric reindexing of its Psi image, using the chosen stdIndex.

**Theorem 1.34 (Standard-sphere barycenter equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryStdSphere_barycenter`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryStdSphere_barycenter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The barycenter class maps to the isometric reindexing of north.

**Theorem 1.35 (Standard-sphere boundary equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryStdSphere_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryStdSphere_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every boundary class maps to the isometric reindexing of south.

**Definition 1.36 (Original face labels).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.FaceIndex`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.FaceIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FaceIndex G face is the subtype of original ground labels belonging to face. All minima and maxima continue to range over this subtype.

**Definition 1.37 (Zero extension into the original ground).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A face vector retains its value at each original face label and has zero coordinate at every original off-face label.

**Theorem 1.38 (Inside-face evaluation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_apply_inside`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_apply_inside` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a label belonging to face, zero extension evaluates to precisely that subtype coordinate.

**Theorem 1.39 (Ghost evaluation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_apply_ghost`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_apply_ghost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a label outside face, zero extension evaluates to zero. Such a label contributes no minimum, maximum or boundary witness.

**Theorem 1.40 (L2 norm of zero extension).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_norm_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindexing the sum of coordinate squares over the face subtype gives the original L2 square; every ghost contributes zero. This does not assert surjectivity onto the enlarged ambient sphere.

**Theorem 1.41 (Membership in the original ambient face).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_faceSimplex`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_faceSimplex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero extension of the L2 transport of an observed face point satisfies the original ground-coordinate nonnegativity, sum-one and off-face-zero equations defining faceSimplex.

**Definition 1.42 (Zero-extension and restriction homeomorphism).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceCoordinateHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceCoordinateHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map from the face-label simplex to the original ambient faceSimplex is zero extension. Its inverse restricts at each original face label. The two coordinate equations prove both inverse laws, and coordinate projections prove continuity in both directions.

**Theorem 1.43 (Literal restriction equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceCoordinateHomeomorph_restrict`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceCoordinateHomeomorph_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the inverse bridge at a face subtype label equals evaluating the ambient representative at that original ground label.

**Definition 1.44 (Full boundary of the ambient face).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceBoundary`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An ambient face point is in the face boundary when some ground label belonging to face has zero coordinate. Off-face zeros are excluded.

**Theorem 1.45 (Boundary compatibility).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceCoordinateHomeomorph_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceCoordinateHomeomorph_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero extension preserves and reflects the boundary condition over face labels, with the original ground-label witnesses retained.

**Definition 1.46 (Ambient full-boundary relation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceBoundarySetoid`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceBoundarySetoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original ambient face quotient identifies exactly equal representatives or two points on this face boundary.

**Theorem 1.47 (Rational formula in ambient coordinates).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_psi_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_psi_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero extension commutes with addition and scalar multiplication in the rational numerator. The scalar denominator and its extrema still use only the face-label coordinates.

**Definition 1.48 (Original ambient quotient homeomorphism).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict an original ambient representative to its face coordinates, apply Psi, and descend through the literal ambient face-boundary relation. The finite convex hull supplies compactness and the same exact-fiber argument gives the homeomorphism to the face-indexed Euclidean sphere.

**Theorem 1.49 (Original ambient representative equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_representative`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every ambient face representative, its quotient image equals Psi of its literal coordinate restriction.

**Theorem 1.50 (Original ambient barycenter equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_barycenter`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_barycenter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The class of the zero-extended face barycenter is sent exactly to the face-indexed north pole.

**Theorem 1.51 (Original ambient boundary equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original ambient face-boundary representative has exactly the face-indexed south image.

**Theorem 1.52 (Ambient vector of an arbitrary class).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_zeroExtend`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_zeroExtend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero-extending the image of a quotient representative is exactly zero-extending the rational formula of its restriction. Original ground labels and ghosts are preserved on both sides.

**Theorem 1.53 (Ambient north coordinate equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_zeroExtend_barycenter`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_zeroExtend_barycenter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The barycenter class has ambient output equal to the zero extension of the normalized face pole.

**Theorem 1.54 (Ambient south coordinate equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_zeroExtend_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_zeroExtend_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A face-boundary class has ambient output equal to the negative zero extension of the normalized face pole.

**Definition 1.55 (Real cardinality).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.cardR`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.cardR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real number obtained by casting the finite face-label cardinality; this is shared by the rational sphere formula and the actual disk collar.

**Theorem 1.56 (Positive nonempty cardinality).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.cardR_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.cardR_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty finite label type, its real cardinality is positive.

**Theorem 1.57 (Nonzero nonempty cardinality).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.cardR_ne`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.cardR_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty finite label type, its real cardinality is nonzero.

**Definition 1.58 (Face-coordinate minimum).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite attained minimum of the actual simplex coordinates over its own label type; it never includes ambient ghosts outside a face.

**Definition 1.59 (The shared barycentric gauge).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the face-coordinate minimum by the real face-label cardinality.

**Theorem 1.60 (An actual minimum label).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every literal finite nonempty simplex point has a label whose coordinate equals the minimum.

**Theorem 1.61 (Minimum below every coordinate).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord_le`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every original simplex label the attained minimum is at most that coordinate.

**Theorem 1.62 (Nonnegative barycentric gauge).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common sigma gauge is nonnegative for every literal simplex point.

**Theorem 1.63 (Full-boundary gauge equation).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty simplex, sigma is zero exactly when some face-label coordinate is zero; the minimum is attained.

**Theorem 1.64 (Continuous face-coordinate minimum).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.continuous_minCoord`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.continuous_minCoord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite coordinate minimum is continuous in the actual L2 simplex topology.

**Theorem 1.65 (Exact barycenter gauge).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.barycenter_gauge`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplexBoundarySphere.barycenter_gauge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the uniform barycenter representative, the shared sigma gauge is exactly one.

**Definition 1.66 (A literal coordinate vertex).**

Lean statement: `D5/S3/Geometry/FiniteSimplexBoundarySphere.vertex`

*Formalization.* `D5/S3/Geometry/FiniteSimplexBoundarySphere.vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual simplex point with coordinate one at the selected label and zero at every other label.

**Theorem 1.67 (A real boundary point when at least two labels exist).**

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
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_barycenter`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_boundary`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_representative`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_zeroExtend`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_zeroExtend_barycenter`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_zeroExtend_boundary`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.barycenter`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.barycenterPoint`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.barycenter_gauge`
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
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.faceCoordinateHomeomorph_restrict`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord_attained`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.minCoord_le`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.nonSouthInverse`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.nonSouthInverse_coordinate`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.north`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.pole`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiDenominator_lower_bound`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiQuotientMap`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiRaw`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psiRaw_norm_sq`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_barycenter`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_boundary`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_eq_iff`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_nonSouthInverse`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_north_iff`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_south_iff`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.psi_surjective`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.reindexSphere`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma_eq_zero_iff`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.sigma_nonneg`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph_barycenter`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph_boundary`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph_representative`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryStdSphere`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryStdSphere_barycenter`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryStdSphere_boundary`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.simplexBoundaryStdSphere_representative`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.south`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.stdIndex`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.vertex`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.vertex_boundary`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_apply_ghost`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_apply_inside`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_faceSimplex`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_norm_sq`
- Truth anchor: `D5/S3/Geometry/FiniteSimplexBoundarySphere.zeroExtend_psi_formula`
- Dependency: [D5/S3/Geometry/EuclideanSphereJoin](EuclideanSphereJoin.md)
- Dependency: [D5/S3/Geometry/FiniteConeCollapse](FiniteConeCollapse.md)
- Dependency: [D5/S3/Geometry/FiniteSimplicialJoin](FiniteSimplicialJoin.md)

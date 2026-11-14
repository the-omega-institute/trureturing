# Positive shapes of entire finite ellipsoids

## Abstract

Positive shapes of entire finite ellipsoids

**Theorem 1.1 (The entire ball determines the shape).**

Lean statement: `D5/S3/Geometry/EllipsoidShape.gram_eq_of_ball_image_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/EllipsoidShape.gram_eq_of_ball_image_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real finite dimensional inner product spaces, equality of the entire images of the closed unit balls under A and B implies equality of A composed with its adjoint and B composed with its adjoint. The source dimensions may differ and either map may have a kernel. A normalized adjoint vector attains the support value. Equal support values and real polarization determine the positive operator.

**Theorem 1.2 (The actual inverse metric).**

Lean statement: `D5/S3/Geometry/EllipsoidShape.metric_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/EllipsoidShape.metric_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If A is injective, the form inner(A x, (A A adjoint) dagger (A y)) equals inner(x,y). The dagger is the existing FiniteMoorePenroseInverse construction. Surjectivity of the adjoint and the first Penrose law give the identity on the source.

**Theorem 1.3 (The range disc and sphere).**

Lean statement: `D5/S3/Geometry/EllipsoidShape.metric_ball_image`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/EllipsoidShape.metric_ball_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership in the whole ball image is equivalent to membership in the actual range of A A adjoint together with inverse-shape quadratic value at most one. The corresponding sphere uses equality to one. The range condition is essential: without it the inequality describes an ambient cylinder.

**Theorem 1.4 (The actual orthogonal projection).**

Lean statement: `D5/S3/Geometry/EllipsoidShape.comp_dagger_eq_projection`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/EllipsoidShape.comp_dagger_eq_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite operator Q, Q composed with its actual Moore-Penrose inverse equals the auxiliary orthogonal projection onto the actual range. The Penrose laws and the defining orthogonality criterion identify this projection.

**Theorem 1.5 (Uniform inverse bound from noncollapse).**

Lean statement: `D5/S3/Geometry/EllipsoidShape.gram_dagger_norm_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/EllipsoidShape.gram_dagger_norm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If eta is positive and eta times norm x is at most norm(A x) for every source vector, the operator norm of the actual inverse of A A adjoint is at most the inverse of eta squared. Coercivity is first proved on the actual range. The Penrose projection controls the ambient input, including null directions.

**Theorem 1.6 (Continuity of actual inverses).**

Lean statement: `D5/S3/Geometry/EllipsoidShape.continuous_dagger_of_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/EllipsoidShape.continuous_dagger_of_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A continuous finite dimensional operator family with uniformly bounded actual Moore-Penrose inverses has a continuous inverse family. Bounded inverse subsequences have convergent subsubsequences. All four Penrose laws pass to the limit, and uniqueness identifies each limit with the actual inverse. This proves continuity without assuming a spectral gap or a chosen eigenbasis.

**Definition 1.7 (The full ambient positive square root).**

Lean statement: `D5/S3/Geometry/EllipsoidShape.positiveSqrt`

*Formalization.* `D5/S3/Geometry/EllipsoidShape.positiveSqrt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive square root is defined through a typed star algebra equivalence from actual operators to real matrices in an orthonormal basis and the pinned matrix continuous functional calculus. It acts on the entire ambient Euclidean space.

**Theorem 1.8 (Positive square-root specification).**

Lean statement: `D5/S3/Geometry/EllipsoidShape.positiveSqrt_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/EllipsoidShape.positiveSqrt_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive shape, its constructed square root is positive, its square is the original operator, and every positive operator with that square is equal to it. These are direct applications of pinned matrix functional calculus through the typed equivalence.

**Theorem 1.9 (Equal shapes give equal entire balls).**

Lean statement: `D5/S3/Geometry/EllipsoidShape.ball_image_eq_of_gram_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/EllipsoidShape.ball_image_eq_of_gram_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal Gram operators imply equal closed-ball images even with unequal source dimensions or ambient null directions. Equal Gram quadratic values give equal adjoint norms. Separation of a point from the compact convex ball image contradicts the equal support bounds.

**Theorem 1.10 (Continuous square roots).**

Lean statement: `D5/S3/Geometry/EllipsoidShape.continuous_positiveSqrt`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/EllipsoidShape.continuous_positiveSqrt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every continuous family of positive finite operators has a continuous full ambient positive square root. The finite dimensional operator-matrix equivalence and its inverse are continuous, and the pinned continuous functional calculus square root is continuous on the positive cone.

**Theorem 1.11 (The whole ambient square-root image).**

Lean statement: `D5/S3/Geometry/EllipsoidShape.positiveSqrt_ball_image`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/EllipsoidShape.positiveSqrt_ball_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every A, the image of the entire ambient closed unit ball under the positive square root of A A adjoint equals the entire original ball image under A. The equality includes all null directions and follows from equality of Gram operators.

**Theorem 1.12 (Positivity of the actual inverse).**

Lean statement: `D5/S3/Geometry/EllipsoidShape.dagger_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/EllipsoidShape.dagger_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual Moore-Penrose inverse of a positive finite shape is positive on the whole ambient Euclidean space and vanishes in null directions. Adjoint transport of the four Penrose laws and uniqueness yield symmetry; the original positive quadratic form then yields inverse positivity.

## References

- Truth anchor: `D5/S3/Geometry/EllipsoidShape.ball_image_eq_of_gram_eq`
- Truth anchor: `D5/S3/Geometry/EllipsoidShape.comp_dagger_eq_projection`
- Truth anchor: `D5/S3/Geometry/EllipsoidShape.continuous_dagger_of_bound`
- Truth anchor: `D5/S3/Geometry/EllipsoidShape.continuous_positiveSqrt`
- Truth anchor: `D5/S3/Geometry/EllipsoidShape.dagger_positive`
- Truth anchor: `D5/S3/Geometry/EllipsoidShape.gram_dagger_norm_bound`
- Truth anchor: `D5/S3/Geometry/EllipsoidShape.gram_eq_of_ball_image_eq`
- Truth anchor: `D5/S3/Geometry/EllipsoidShape.metric_ball_image`
- Truth anchor: `D5/S3/Geometry/EllipsoidShape.metric_pullback`
- Truth anchor: `D5/S3/Geometry/EllipsoidShape.positiveSqrt`
- Truth anchor: `D5/S3/Geometry/EllipsoidShape.positiveSqrt_ball_image`
- Truth anchor: `D5/S3/Geometry/EllipsoidShape.positiveSqrt_spec`
- Dependency: [D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance](../Observer/Hilbert/FiniteSynthesisGramDistance.md)

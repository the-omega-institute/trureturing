# Euclidean sphere joins

## Abstract

The ordinary topological join of actual Euclidean unit spheres.

**Definition 1.1 (Unit spheres).**

Lean statement: `D5/S3/Geometry/EuclideanSphereJoin.UnitSphere`

*Formalization.* `D5/S3/Geometry/EuclideanSphereJoin.UnitSphere` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unit sphere is the actual metric sphere of radius one about zero, equipped with its normed-space subspace topology.

**Definition 1.2 (Standard Euclidean spheres).**

Lean statement: `D5/S3/Geometry/EuclideanSphereJoin.StdSphere`

*Formalization.* `D5/S3/Geometry/EuclideanSphereJoin.StdSphere` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural n, the standard sphere is the unit sphere in EuclideanSpace over the reals indexed by Fin (n+1), with the Euclidean norm. In particular n=0 is the two-point sphere in a one-dimensional vector space.

**Definition 1.3 (Normalized block coordinates).**

Lean statement: `D5/S3/Geometry/EuclideanSphereJoin.representative`

*Formalization.* `D5/S3/Geometry/EuclideanSphereJoin.representative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For unit vectors x and y and t in the closed unit interval, put d=max(1-t,t). The representative map is the pair (((1-t)/d)x,(t/d)y). The positive denominator is at least one half. The product carries its native maximum norm, so the resulting vector has norm one.

**Theorem 1.4 (The exact ordinary join relation).**

Lean statement: `D5/S3/Geometry/EuclideanSphereJoin.representative_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/EuclideanSphereJoin.representative_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real normed spaces E and F and all actual representatives a and b in S(E) times S(F) times the closed unit interval, their normalized block vectors agree if and only if their interval coordinates agree, their left coordinates agree unless the parameter is one, and their right coordinates agree unless it is zero. The block norms recover the two nonnegative weights, and the right weight divided by the sum of the weights recovers the parameter. A nonzero weight can be cancelled, while the endpoint block vanishes.

**Definition 1.5 (Descent to the actual quotient).**

Lean statement: `D5/S3/Geometry/EuclideanSphereJoin.productSphereMap`

*Formalization.* `D5/S3/Geometry/EuclideanSphereJoin.productSphereMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The continuous normalized block formula descends through FiniteSimplicialJoin.OrdinaryJoin, using exactly its endpoint setoid and native quotient topology.

**Definition 1.6 (The maximum norm sphere).**

Lean statement: `D5/S3/Geometry/EuclideanSphereJoin.productSphereHomeomorph`

*Formalization.* `D5/S3/Geometry/EuclideanSphereJoin.productSphereHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For compact unit spheres with chosen actual points x0 and y0, the ordinary join is homeomorphic to the unit sphere of the product. Given a target (u,v), write r=norm(u), s=norm(v). Its maximum block norm is one. Choose t=s/(r+s), normalize each nonzero block and use x0 or y0 for a zero block. This gives a preimage without requiring the choices to be continuous. Exact fibers give injectivity. The quotient is compact and the target is Hausdorff, so the native continuous bijection is a homeomorphism.

**Definition 1.7 (Chosen coordinate points).**

Lean statement: `D5/S3/Geometry/EuclideanSphereJoin.coordinatePoint`

*Formalization.* `D5/S3/Geometry/EuclideanSphereJoin.coordinatePoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The chosen point of each standard sphere is the first coordinate vector, with coefficient one in coordinate zero and zero elsewhere.

**Definition 1.8 (The Euclidean sphere join homeomorphism).**

Lean statement: `D5/S3/Geometry/EuclideanSphereJoin.sphereJoinHomeomorph`

*Formalization.* `D5/S3/Geometry/EuclideanSphereJoin.sphereJoinHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every pair of natural p and q, the ordinary join of the actual standard Euclidean spheres of dimensions p and q is homeomorphic to the actual standard Euclidean sphere of dimension p+q+1. The normalized quotient homeomorphism first reaches the maximum-norm product sphere. Native linear coordinate concatenation identifies the ambient product with the Euclidean space indexed by Fin (p+q+2). Radial normalization sends z to L(z)/norm(L(z)); the inverse sends w to L inverse(w)/norm(L inverse(w)). Nonzero images, linearity and scalar norm identities prove that the maps are inverse, and the native polar-coordinate homeomorphism supplies their continuity. No equality between the product maximum norm and the Euclidean norm is used. Both zero-dimensional sphere factors are included. Hatcher, Algebraic Topology, page 9 defines the ordinary join, and Chapter 0 Exercise 18 on page 19 states this classical sphere identity. This construction supplies a classical geometric bridge and makes no claim to resolve Carnero Bravo Question 22.

**Theorem 1.9 (Exact coordinate endpoint).**

Lean statement: `D5/S3/Geometry/EuclideanSphereJoin.sphereJoinHomeomorph_coordinatePoint`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/EuclideanSphereJoin.sphereJoinHomeomorph_coordinatePoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural p and q and every actual point y of the q-dimensional sphere, the homeomorphism sends the quotient class of (e0,y,0) exactly to the first coordinate unit vector of the target sphere. At parameter zero the normalized product vector is (e0,0). Concatenation sends it to the first target coordinate vector, whose Euclidean norm is one, so radial normalization fixes it.

## References

- Truth anchor: `D5/S3/Geometry/EuclideanSphereJoin.StdSphere`
- Truth anchor: `D5/S3/Geometry/EuclideanSphereJoin.UnitSphere`
- Truth anchor: `D5/S3/Geometry/EuclideanSphereJoin.coordinatePoint`
- Truth anchor: `D5/S3/Geometry/EuclideanSphereJoin.productSphereHomeomorph`
- Truth anchor: `D5/S3/Geometry/EuclideanSphereJoin.productSphereMap`
- Truth anchor: `D5/S3/Geometry/EuclideanSphereJoin.representative`
- Truth anchor: `D5/S3/Geometry/EuclideanSphereJoin.representative_eq_iff`
- Truth anchor: `D5/S3/Geometry/EuclideanSphereJoin.sphereJoinHomeomorph`
- Truth anchor: `D5/S3/Geometry/EuclideanSphereJoin.sphereJoinHomeomorph_coordinatePoint`
- Dependency: [D5/S3/Geometry/FiniteSimplicialJoin](FiniteSimplicialJoin.md)

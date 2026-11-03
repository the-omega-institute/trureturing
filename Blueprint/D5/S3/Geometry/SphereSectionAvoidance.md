# Finite avoidance on round spheres

## Abstract

Finite affine-section and collision avoidance in open patches of round spheres.

The construction uses classical rational circle coordinates, finite unions of proper linear kernels and finiteness of the roots of a nonzero polynomial. The finite-union and root-finiteness results are reused from Mathlib. The carrier dimension is at least two and the radius is positive. Two-point spheres are outside these avoidance statements.

**Definition 1.1 (Rational circle coordinates).**

Lean statement: `D5/S3/Geometry/SphereSectionAvoidance.circleArc`

*Formalization.* `D5/S3/Geometry/SphereSectionAvoidance.circleArc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For vectors x and v and real t, the arc is ((1-t squared)/(1+t squared)) times x plus (2t/(1+t squared)) times v. If x and v are perpendicular and have the same positive norm, every point of the arc has that norm. The parameter zero gives x.

**Theorem 1.2 (Every nonempty open patch avoids finitely many affine hyperplanes).**

Lean statement: `D5/S3/Geometry/SphereSectionAvoidance.exists_on_sphere_avoiding_sections`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/SphereSectionAvoidance.exists_on_sphere_avoiding_sections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be any finite-dimensional real inner product space of dimension at least two, let r be positive, and let U be ambient-open with a point of norm r. For any finite family of nonzero normals a and arbitrary real offsets b, there is a point y in U of norm r with inner product of a(i) and y different from b(i) for every index. A tangent direction is selected to avoid all homogeneous sections passing through the starting point. Each remaining forbidden equation pulls back to a nonzero polynomial of degree at most two. A small interval of parameters stays in U and misses their finite root union.

**Theorem 1.3 (Unit spheres and collisions in an actual affine carrier).**

Lean statement: `D5/S3/Geometry/SphereSectionAvoidance.exists_on_affine_sphere_avoiding`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/SphereSectionAvoidance.exists_on_affine_sphere_avoiding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a linear subspace of a finite-dimensional real inner product space, with dimension at least two, c an arbitrary center and R a positive radius. Every ambient-open patch containing some c+w with w in K of norm R contains such a point avoiding finitely many unit spheres and finitely many specified collision points. For every unit-sphere center z, the precise properness hypothesis says that if the orthogonal projection of z-c into K vanishes, then R squared plus norm(z-c) squared differs from one. Nonzero projected normals use affine-section avoidance; zero normals have a nonzero constant equation. Collision exclusions are encoded by inner products, with the center c excluded directly by the positive radius. All the finite families may be empty. This proves a geometric supplier; it does not assert a graph-realization or a restoration theorem.

## References

- Truth anchor: `D5/S3/Geometry/SphereSectionAvoidance.circleArc`
- Truth anchor: `D5/S3/Geometry/SphereSectionAvoidance.exists_on_affine_sphere_avoiding`
- Truth anchor: `D5/S3/Geometry/SphereSectionAvoidance.exists_on_sphere_avoiding_sections`

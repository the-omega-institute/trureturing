# Product cones and Jordan squares

## Abstract

Generalized doubly nonnegative cones on orthant and Lorentz products.

**Definition 1.1 (Product coordinates).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Defs.Idx`

*Formalization.* `D5/S3/QuadraticForms/ConicGDNN/Defs.Idx` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Orthant coordinates and the time and spatial coordinates of each Lorentz block form one finite index type.

**Definition 1.2 (The product cone).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Defs.cone`

*Formalization.* `D5/S3/QuadraticForms/ConicGDNN/Defs.cone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each orthant coordinate is nonnegative, and each block time dominates the Euclidean length of its spatial part. Zero-dimensional spatial parts are allowed.

**Definition 1.3 (The standard dual cone).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Defs.dualCone`

*Formalization.* `D5/S3/QuadraticForms/ConicGDNN/Defs.dualCone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The standard coordinate pairing is nonnegative against every member of the given cone.

**Definition 1.4 (Extreme ray generators).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Defs.extremeRays`

*Formalization.* `D5/S3/QuadraticForms/ConicGDNN/Defs.extremeRays` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A nonzero cone member generates an extreme ray when every cone decomposition has its first summand on the same nonnegative ray.

**Definition 1.5 (The Jordan square).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Defs.jsq`

*Formalization.* `D5/S3/QuadraticForms/ConicGDNN/Defs.jsq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Orthant entries are squared. Each block becomes the sum of its coordinate squares in time and twice time times space in each spatial entry.

**Definition 1.6 (Homogeneous quartic sums of squares).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Defs.sos4`

*Formalization.* `D5/S3/QuadraticForms/ConicGDNN/Defs.sos4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The convex hull of squares of homogeneous quadratic polynomials is the chosen quartic sum of squares cone.

**Definition 1.7 (Matrix pullback along the Jordan square).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Defs.quartic`

*Formalization.* `D5/S3/QuadraticForms/ConicGDNN/Defs.quartic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix is paired with two copies of the polynomial Jordan square.

**Definition 1.8 (The zeroth copositive approximation).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Defs.knn0`

*Formalization.* `D5/S3/QuadraticForms/ConicGDNN/Defs.knn0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A symmetric matrix belongs when its quartic pullback is in the chosen sum of squares cone.

**Definition 1.9 (The dual approximation).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Defs.dnnNN`

*Formalization.* `D5/S3/QuadraticForms/ConicGDNN/Defs.dnnNN` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A symmetric matrix has nonnegative trace pairing with every matrix in the zeroth approximation.

**Definition 1.10 (The extreme ray preserving cone).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Defs.dnnBD`

*Formalization.* `D5/S3/QuadraticForms/ConicGDNN/Defs.dnnBD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A matrix is positive semidefinite and maps every extreme ray generator of the dual cone into the original cone.

**Definition 1.11 (The cone inclusion).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Defs.claim`

*Formalization.* `D5/S3/QuadraticForms/ConicGDNN/Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite orthant and finite product of Lorentz blocks with positive spatial dimensions, the dual approximation is contained in the extreme ray preserving cone.

## References

- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Defs.Idx`
- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Defs.claim`
- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Defs.cone`
- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Defs.dnnBD`
- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Defs.dnnNN`
- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Defs.dualCone`
- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Defs.extremeRays`
- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Defs.jsq`
- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Defs.knn0`
- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Defs.quartic`
- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Defs.sos4`

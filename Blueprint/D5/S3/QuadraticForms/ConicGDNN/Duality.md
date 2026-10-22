# Sum of squares tests and cone duality

## Abstract

Dual trace positivity implies positive semidefiniteness and preservation of the product cone.

**Theorem 1.1 (Rank-one tests).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Duality.quartic_rankOne`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/ConicGDNN/Duality.quartic_rankOne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real coordinate vector w, the symmetric rank-one matrix ww-transpose belongs to the zeroth approximation. Its quartic pullback is the square of the homogeneous quadratic polynomial obtained by pairing w with the Jordan square.

**Theorem 1.2 (Positive semidefiniteness).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Duality.posSemidef_of_mem_dnnNN`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/ConicGDNN/Duality.posSemidef_of_mem_dnnNN` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A matrix in the dual approximation is positive semidefinite: testing its trace pairing on every rank-one matrix gives a nonnegative quadratic form. Symmetry is part of the definition of the dual approximation.

**Theorem 1.3 (Products of cone pullbacks).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Duality.sym_mem_knn0`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/ConicGDNN/Duality.sym_mem_knn0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For u and v in the product cone, half the sum of uv-transpose and vu-transpose belongs to the zeroth approximation. The Lorentz certificates express both pullbacks as sums of squares of homogeneous linear polynomials. Their product is a sum of squares of homogeneous quadratics. Nonnegative scaling preserves the convex hull of quadratic squares, so finite sums belong to this convex hull.

**Theorem 1.4 (Preservation of the entire product cone).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Duality.mulVec_mem_cone`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/ConicGDNN/Duality.mulVec_mem_cone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a matrix belongs to the dual approximation, multiplying any product-cone vector by that matrix gives another product-cone vector. Trace positivity on the symmetric tests gives nonnegative pairings with every cone member. Self-duality of the product cone then yields the conclusion, including empty orthants and blocks with zero spatial dimension.

## References

- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Duality.mulVec_mem_cone`
- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Duality.posSemidef_of_mem_dnnNN`
- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Duality.quartic_rankOne`
- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Duality.sym_mem_knn0`
- Dependency: [D5/S3/QuadraticForms/ConicGDNN/Lorentz](Lorentz.md)

# Charged collision current moments

## Abstract

Charged collision current moments.

**Theorem 1.1 (The closed corrected-source recurrence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Current.source_closed_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Current.source_closed_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every signed exponent and actual tensor input, the corrected creation sequence obeys the closed current recurrence, with its one-half norm term and finite bilinear lower-order terms.

**Definition 1.2 (The finite normal-current moment).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Current.collisionMoment`

*Formalization.* `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Current.collisionMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The moment weights each finite creator diagonal by one half of the difference between the second creator degree and the second translation degree, on the actual translated polynomial support.

**Theorem 1.3 (The arbitrary-input normal-current calculation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Current.collision_normal_moment`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Current.collision_normal_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normal current of collisionField on p tensor g equals the scalar-weighted collisionMoment tensor the actual ground action. The negative branch uses the creation differential equation; the nonnegative branch differentiates the full translated polynomial and counts repeated variables. All ranks and charges, including zero, remain in scope.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Current.collisionMoment`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Current.collision_normal_moment`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Current.source_closed_recurrence`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel](Kernel.md)

# The Abstract Spatial Equation Criterion

## Abstract

Principal right multiples characterize spatial equations, with uniqueness in a domain.

**Theorem 1.1 (Principal-multiple membership and unique nonzero solutions).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/SpatialEquationCriterion.spatial_equation_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/SpatialEquationCriterion.spatial_equation_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a unital ring, the equation f * g = h is solvable exactly when h is a right multiple of f. In a ring without zero divisors, a nonzero f has at most one such solution; when f is zero, solvability is exactly h = 0 and every g solves the equation. The statement records these membership and cancellation guards without introducing a division algorithm.

**Theorem 1.2 (The principal-multiple carrier is closed under subtraction).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/SpatialEquationCriterion.principalMultiples_sub`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/SpatialEquationCriterion.principalMultiples_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differences of principal multiples remain principal multiples by distributivity. This is a closure property of a general ring; computing a quotient is a separate question.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/SpatialEquationCriterion.principalMultiples_sub`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/SpatialEquationCriterion.spatial_equation_criterion`

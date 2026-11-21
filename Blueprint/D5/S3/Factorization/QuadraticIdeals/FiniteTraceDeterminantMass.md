# Trace laws over finite fields

## Abstract

Actual trace fibers and exact uniform mass for a fixed nonzero determinant.

**Theorem 1.1 (Trace and determinant fibers reduce to a quadratic root count).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/FiniteTraceDeterminantMass.matrix_trace_det_fiber_card`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/FiniteTraceDeterminantMass.matrix_trace_det_fiber_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first diagonal coordinate fixes the other. The two off-diagonal coordinates must have a specified product, giving an explicit cardinality decomposition.

**Theorem 1.2 (The quadratic character gives the exact trace fiber size).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/FiniteTraceDeterminantMass.matrix_trace_det_quadratic_character_card`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/FiniteTraceDeterminantMass.matrix_trace_det_quadratic_character_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Completing the square identifies the remaining quadratic roots with the square roots of the characteristic discriminant in the actual odd finite field.

**Theorem 1.3 (Every nonzero determinant fiber has the special linear group size).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/FiniteTraceDeterminantMass.det_fiber_card`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/FiniteTraceDeterminantMass.det_fiber_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Scaling the first row by the inverse determinant gives a bijection to the special linear group, with no choice of a matrix representative.

**Theorem 1.4 (Uniform conditional trace mass is an exact rational ratio).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/FiniteTraceDeterminantMass.uniform_trace_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/FiniteTraceDeterminantMass.uniform_trace_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace-fiber cardinality divided by the determinant-fiber cardinality is the exact finite conditionally uniform law. It provides a counting input for arithmetic readouts, not a theorem of Frobenius equidistribution.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/FiniteTraceDeterminantMass.det_fiber_card`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/FiniteTraceDeterminantMass.matrix_trace_det_fiber_card`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/FiniteTraceDeterminantMass.matrix_trace_det_quadratic_character_card`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/FiniteTraceDeterminantMass.uniform_trace_mass`

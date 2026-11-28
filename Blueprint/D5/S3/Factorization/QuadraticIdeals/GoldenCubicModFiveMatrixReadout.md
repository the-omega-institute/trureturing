# Exact finite matrix certificates modulo five

## Abstract

Finite F5 matrix powers and normalized traces give uniformly calibrated Frobenius readouts.

**Theorem 1.1 (The noncentral repeated-root class has exact projective order five).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModFiveMatrixReadout.projective_five_of_noncentral_repeated_root`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModFiveMatrixReadout.projective_five_of_noncentral_repeated_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For determinant one and trace squared four, a nonscalar matrix first becomes scalar at the fifth positive power. The finite certificate uses the same powers as matrix multiplication.

**Theorem 1.2 (Both nonsquare determinant fibers have the same normalized trace law).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModFiveMatrixReadout.nonsquare_fibers_normalized_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModFiveMatrixReadout.nonsquare_fibers_normalized_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant-three trace is multiplied by two. The five normalized trace counts, in order zero through four, are 20, 20, 30, 30 and 20 in each nonsquare determinant fiber.

**Theorem 1.3 (Three trace conditions read the exact projective order).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModFiveMatrixReadout.exact_nonsquare_projective_length`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModFiveMatrixReadout.exact_nonsquare_projective_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonsquare determinant the least positive scalar power is two for zero trace, four when the trace squared is twice the determinant, and six otherwise. The finite check excludes every smaller positive scalar power.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModFiveMatrixReadout.exact_nonsquare_projective_length`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModFiveMatrixReadout.nonsquare_fibers_normalized_trace`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModFiveMatrixReadout.projective_five_of_noncentral_repeated_root`

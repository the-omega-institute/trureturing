# Cayley-Hamilton gives the exact universal sixth power

## Abstract

The Cayley-Hamilton sixth power detects a nontrivial mod-nine congruence direction.

**Theorem 1.1 (Cayley-Hamilton gives the exact universal sixth power).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness.sixth_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness.sixth_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For determinant one and trace four or five, the Cayley-Hamilton cubic collapses to an affine expression modulo nine.

**Theorem 1.2 (The sixth power is nontrivial modulo nine).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness.sixth_not_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness.sixth_not_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If it were trivial, the entry constraints would force the characteristic discriminant to be zero modulo nine, contradicting either trace.

**Theorem 1.3 (The sixth power reduces to identity modulo three).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness.sixth_reduces_to_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness.sixth_reduces_to_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit scalar coefficients vanish or become one in the residue field.

**Theorem 1.4 (The trace-four companion sixth power is explicit).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness.companion_four_sixth`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness.companion_four_sixth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two-by-two identity holds over the ring modulo nine, not only in the residue field.

**Theorem 1.5 (The trace-five companion sixth power is explicit).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness.companion_five_sixth`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness.companion_five_sixth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second trace case has its own exact companion certificate.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness.companion_five_sixth`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness.companion_four_sixth`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness.sixth_formula`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness.sixth_not_identity`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness.sixth_reduces_to_identity`

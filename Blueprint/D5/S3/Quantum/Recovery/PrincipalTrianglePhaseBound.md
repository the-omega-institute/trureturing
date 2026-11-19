# Near-real phase bound for principal quantum recovery

## Abstract

Principal Gram data and cross-overlap dominance give a quadratic error penalty.

**Theorem 1.1 (Phase obstruction from cross-entry dominance).**

Lean statement: `D5/S3/Quantum/Recovery/PrincipalTrianglePhaseBound.triangle_imag_of_cross_dominance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PrincipalTrianglePhaseBound.triangle_imag_of_cross_dominance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive Gram completion fills defects only inside each two-dimensional fibre and preserves every cross entry. If the first record does not exceed the second in cross-entry modulus, a matrix-unit error below one quarter forces a quantitative non-real triangle in the second record. A positive correlation quotient with unit diagonal implies, but is not needed to state, this modulus dominance.

**Theorem 1.2 (Quadratic penalty for near-real triangles).**

Lean statement: `D5/S3/Quantum/Recovery/PrincipalTrianglePhaseBound.near_real_error_lower_of_cross_dominance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PrincipalTrianglePhaseBound.near_real_error_lower_of_cross_dominance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If all eight absolute triangle imaginary parts are at most eta, the matrix-unit error is at least one quarter minus 128 eta squared over 27. The constant is a closed-form corollary of the phase bound, not a claimed optimum for unrestricted quantum channels.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PrincipalTrianglePhaseBound.near_real_error_lower_of_cross_dominance`
- Truth anchor: `D5/S3/Quantum/Recovery/PrincipalTrianglePhaseBound.triangle_imag_of_cross_dominance`
- Dependency: [D5/S3/Quantum/Recovery/PrincipalTrianglePhaseGeometry](PrincipalTrianglePhaseGeometry.md)

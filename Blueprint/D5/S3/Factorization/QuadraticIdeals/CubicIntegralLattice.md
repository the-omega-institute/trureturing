# Two-prime saturation of integral lattices

## Abstract

An integral trace lattice can be saturated using two Eisenstein witnesses and one coprime scalar.

**Theorem 1.1 (The trace discriminant clears every integral element into the lattice).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/CubicIntegralLattice.discr_smul_mem_integral_span`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicIntegralLattice.discr_smul_mem_integral_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an integral rational basis, the trace matrix has integral entries. Cramer’s rule writes the discriminant times an integral element with integer basis coefficients. Closure under products is not assumed for the lattice.

**Theorem 1.2 (The companion and its translate supply global saturation).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/CubicIntegralLattice.integral_span_of_eisenstein_translate`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicIntegralLattice.integral_span_of_eisenstein_translate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A clearing scalar puts the integral lattice into the monogenic order. Two Eisenstein conditions remove the denominator primes, and a Bezout identity recovers the original element in the larger lattice.

**Theorem 1.3 (One sheared denominator rescales the trace determinant).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/CubicIntegralLattice.trace_det_single_denominator`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicIntegralLattice.trace_det_single_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The third basis vector may absorb integer combinations of the first two and be divided by P. The corresponding row and column changes multiply the trace determinant by 1/P squared.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicIntegralLattice.discr_smul_mem_integral_span`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicIntegralLattice.integral_span_of_eisenstein_translate`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicIntegralLattice.trace_det_single_denominator`

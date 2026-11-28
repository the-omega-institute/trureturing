# The centered prime Mellin moment

## Abstract

A zero Mellin moment for centered prime dilations

**Theorem 1.1 (Unconditional decay of the centered prime sum).**

Lean statement: `D5/S3/Weil/Analytic/NymanCenteredMomentTail.centeredPrime_log_cube_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanCenteredMomentTail.centeredPrime_log_cube_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Partial summation transfers fourth-logarithmic Möbius decay to the compact dilation kernel. The centered logarithmic identity then bounds the prime sum by a constant times x divided by the third power of log x.

**Theorem 1.2 (The absolutely convergent zero moment).**

Lean statement: `D5/S3/Weil/Analytic/NymanCenteredMoment.integral_centeredPrime_weighted_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanCenteredMoment.integral_centeredPrime_weighted_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weighting the centered prime sum by the inverse square of x gives an absolutely convergent integral on the interval from one to infinity. The prime number theorem gives zero normalized residue for the centered Dirichlet series. Mellin factorization and dominated convergence give the value zero for the ordinary integral.

## References

- Truth anchor: `D5/S3/Weil/Analytic/NymanCenteredMoment.integral_centeredPrime_weighted_eq_zero`
- Truth anchor: `D5/S3/Weil/Analytic/NymanCenteredMomentTail.centeredPrime_log_cube_bound`

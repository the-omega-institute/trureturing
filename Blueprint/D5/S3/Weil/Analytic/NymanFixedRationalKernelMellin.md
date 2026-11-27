# Mellin transform of the rational cubic kernel

## Abstract

Mellin transform of the rational cubic kernel

**Theorem 1.1 (Exact Mellin product).**

Lean statement: `D5/S3/Weil/Analytic/NymanFixedRationalKernelMellin.mellin_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanFixedRationalKernelMellin.mellin_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the half-plane Re(s) > 0, the transform of the real kernel is the product of a^(s+j) − 1 from j = 0 through 3 divided by s(s+1)(s+2)(s+3), with a = 7/6. Integration on each truncated cubic gives endpoint terms whose upper contributions cancel.

**Theorem 1.2 (Nonvanishing in the right half-plane).**

Lean statement: `D5/S3/Weil/Analytic/NymanFixedRationalKernelMellin.mellin_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanFixedRationalKernelMellin.mellin_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each power a^(s+j) has modulus a^(Re(s)+j) > 1 in this half-plane, and the four denominator factors are nonzero.

## References

- Truth anchor: `D5/S3/Weil/Analytic/NymanFixedRationalKernelMellin.mellin_formula`
- Truth anchor: `D5/S3/Weil/Analytic/NymanFixedRationalKernelMellin.mellin_ne_zero`
- Dependency: [D5/S3/Weil/Analytic/NymanFixedRationalKernel](NymanFixedRationalKernel.md)

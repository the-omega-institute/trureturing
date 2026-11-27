# The explicit rational cubic kernel

## Abstract

The explicit rational cubic kernel

**Definition 1.1 (Exact rational evaluation).**

Lean statement: `D5/S3/Weil/Analytic/NymanFixedRationalKernel.bRat`

*Formalization.* `D5/S3/Weil/Analytic/NymanFixedRationalKernel.bRat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a = 7/6, take the five coefficients of (1 − z)(1 − az)(1 − a²z)(1 − a³z) in increasing degree order. The rational kernel is one sixth of the sum of each coefficient times the cube of max(u/aʲ − 1, 0) for j from zero to four.

**Theorem 1.2 (Agreement with the real kernel).**

Lean statement: `D5/S3/Weil/Analytic/NymanFixedRationalKernel.bRat_cast`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanFixedRationalKernel.bRat_cast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Casting the rational evaluation to the reals gives the real cubic kernel at the same rational input.

**Theorem 1.3 (Support inside the first shell).**

Lean statement: `D5/S3/Weil/Analytic/NymanFixedRationalKernel.b_zero_off`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanFixedRationalKernel.b_zero_off` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All positive parts vanish at or below 1. At or above a⁴ the untruncated cubic terms cancel, and a⁴ < 2. Thus the kernel vanishes outside the open interval (1, 2).

**Theorem 1.4 (The four difference factors).**

Lean statement: `D5/S3/Weil/Analytic/NymanFixedRationalKernel.coefficient_product`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanFixedRationalKernel.coefficient_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient polynomial factors into the four linear factors of the dilation difference.

## References

- Truth anchor: `D5/S3/Weil/Analytic/NymanFixedRationalKernel.bRat`
- Truth anchor: `D5/S3/Weil/Analytic/NymanFixedRationalKernel.bRat_cast`
- Truth anchor: `D5/S3/Weil/Analytic/NymanFixedRationalKernel.b_zero_off`
- Truth anchor: `D5/S3/Weil/Analytic/NymanFixedRationalKernel.coefficient_product`

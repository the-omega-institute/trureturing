# The 142857 repeating-decimal quotient certificate

## Abstract

The six-digit repeating-decimal shift and quotient certificate for one seventh.

**Theorem 1.1 (Six-digit shift and period quotient).**

Lean statement: `D5/S3/Arith/RepeatingDecimalQuotient.repeating_decimal_142857_shift_quotient`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RepeatingDecimalQuotient.repeating_decimal_142857_shift_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over the rationals, shifting the generator 1/7 by six decimal places gives 142857 after subtracting the original generator, and dividing 142857 by the period kernel 999999 returns 1/7. This is the exact arithmetic certificate used by the chapter example; it does not add a separate analytic definition of an infinite decimal expansion.

## References

- Truth anchor: `D5/S3/Arith/RepeatingDecimalQuotient.repeating_decimal_142857_shift_quotient`

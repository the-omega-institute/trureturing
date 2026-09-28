# Contracting Digit Memory

## Abstract

Binary contracting digits have an exact finite-state accuracy law.

**Theorem 1.1 (The exact state count for contracting binary digits).**

Lean statement: `D5/S3/Observer/MetricGeometry/ContractingDigitMemory.contracting_digit_memory_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/ContractingDigitMemory.contracting_digit_memory_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the contraction parameter lambda be positive and less than one half. Encode every infinite binary stream as the real number obtained from the normalized geometric digit series, and let an action prepend a bit to the stream. For an integer L at least one and an error epsilon between lambda to the power L divided by two and (1 minus lambda) times lambda to the power L minus one divided by two, the least number of states of a finite predictor with this readout and action is exactly 2 to the power L.

The upper bound stores the first L bits. Each action inserts its bit at the front and drops the last stored bit; the corresponding prefix class has radius lambda to the power L, and its midpoint gives the required error.

For the lower bound, the 2 to the power L zero-tail prefixes are separated by at least (1 minus lambda) times lambda to the power L minus one. Two such prefixes mapped to one finite state would therefore incur total error at least that separation, contradicting the strict upper error bound. The special value epsilon equal to lambda to the power L divided by two gives the same exact state count for arbitrarily long action words.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/ContractingDigitMemory.contracting_digit_memory_exact`
- Dependency: [D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover](ForwardInvariantPredictorCover.md)

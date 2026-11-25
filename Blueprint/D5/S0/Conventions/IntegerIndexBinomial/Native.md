# Integer lower indices in executable sums

## Abstract

The executable binomial coefficient accepts an integer lower index.

**Definition 1.1 (The native binomial coefficient).**

$$B(m,j) = if j < 0 then 0 else \operatorname{choose}(m,j)$$

*Formalization.* `D5/S0/Conventions/IntegerIndexBinomial/Native.binom_std` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a negative lower index the function returns zero. For a nonnegative index it computes Mathlib’s natural binomial coefficient and returns its integer value. The executable ballot coefficient subtracts the values at two adjacent integer indices.

## References

- Truth anchor: `D5/S0/Conventions/IntegerIndexBinomial/Native.binom_std`

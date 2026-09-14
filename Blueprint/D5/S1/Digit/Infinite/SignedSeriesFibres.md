# The Fibres of the Signed Golden Series

## Abstract

The Fibres of the Signed Golden Series.

**Theorem 1.1 (Two streams at each seam).**

Lean statement: `D5/S1/Digit/Infinite/SignedSeriesFibres.signed_series_fibres`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SignedSeriesFibres.signed_series_fibres` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write legal infinite digits as blocks zero and one followed by zero. For every finite block word w, including the empty word, its affine image of minus alpha cubed has exactly two distinct streams: w followed by the zero block and the upper alternating stream, and w followed by the one-zero block and that same alternating stream. Different words give different seam values. Every other value in the closed interval from minus alpha to alpha squared has exactly one stream.

## References

- Truth anchor: `D5/S1/Digit/Infinite/SignedSeriesFibres.signed_series_fibres`
- Dependency: [D5/S0/Automata/BinaryZeckendorfBlockSkeletonCore](../../../S0/Automata/BinaryZeckendorfBlockSkeletonCore.md)
- Dependency: [D5/S1/Digit/Infinite/SignedSeriesRange](SignedSeriesRange.md)

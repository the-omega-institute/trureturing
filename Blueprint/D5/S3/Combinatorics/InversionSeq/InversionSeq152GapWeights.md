# Separation of Internal and Final Gap Weights

## Abstract

Weights on successive increases separate the last positive increase from all earlier increases.

**Theorem 1.1 (Isolating the final increase).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152GapWeights.gap_weight_isolation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152GapWeights.gap_weight_isolation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Let I and T be nonnegative integer-valued functions with I(0) = T(0) = 0. For a weakly increasing word whose entries are at least a given preceding value p, form the successive differences after adjoining p and discard the zero differences. Weight each original difference by T when its destination is the maximum entry and by I otherwise, using p as the maximum for the empty word. The total equals the sum of I over all positive differences except the last, plus T of the last positive difference, with zero used when there is none.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152GapWeights.gap_weight_isolation`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152GapCount](InversionSeq152GapCount.md)

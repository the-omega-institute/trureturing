# Matched Bell comparison for diagonal-reset qutrit compression

## Abstract

An arbitrary decoder after a plane-preserving diagonal reset has a matched Bell block that dominates an explicitly attainable nonnegative block entry by entry.

**Theorem 1.1 (An actual channel attains the matched block bound).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalReset.diagonal_reset_bell_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalReset.diagonal_reset_bell_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kohtaro Kato (2025). *Exact and Local Compression of Quantum Bipartite States*. DOI: [10.1109/TIT.2025.3562884](https://doi.org/10.1109/TIT.2025.3562884). URL: <https://arxiv.org/abs/2309.07434>.

*Commentary.*

The source is the normalized qutrit Bell state. The reference factor stays untouched, and a fixed encoder and decoder communicate solely through the qubit. The encoder acts identically on the first two levels, erases their coherences with the third level, and resets that level to a diagonal memory state. The matched block consists of the real parts of the joint state difference on the three vectors |ii>, multiplied by three. Order the kept levels so that the less reliably matched level is second, and let x be the square root of its matched output probability. Choi positivity bounds the real matched coherence by the product of the square roots of the two matched probabilities. Trace preservation bounds the probability sent to the discarded level from either kept level by one minus that level's matched probability. The resulting lower matrix has diagonal (0, 1 - x squared, x squared) and upper off-diagonal entries (1 - x, 1, 1). Resetting to the second level and using the two-Kraus decoder with amplitudes x and the square root of one minus x squared gives exactly this matched block.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalReset.diagonal_reset_bell_comparison`
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Recovery/LocalCompression/QutritPure](QutritPure.md)

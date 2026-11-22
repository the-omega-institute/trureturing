# The relative entropy cost of a reference increment

## Abstract

A sharp spectral lower bound on the cost of adding a zero-likelihood class to a reference state.

**Theorem 1.1 (Lower bound from the smallest reference eigenvalue).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.log_increment_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.log_increment_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Koenraad M. R. Audenaert (2014). *Quantum Skew Divergence*. DOI: [10.1063/1.4901039](https://doi.org/10.1063/1.4901039). URL: <https://arxiv.org/abs/1304.5935v2>.

*Commentary.*

The comparison dominates u times the positive reference C, and C has spectral floor lambda. Adding a trace-one positive density with weight e to the reference decreases the trace-log relative entropy of the fixed comparison by at least u times lambda times log(1 + e/lambda). The proof differentiates the logarithm along the affine reference path, compares the comparison to a positive multiple of the current reference, and uses the trace identity for the resolvent derivative. Audenaert's logarithm calculation supplies the analytic prerequisite.

**Theorem 1.2 (Attainment at a lowest eigenvector).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.log_increment_eq_of_eigenvector`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.log_increment_eq_of_eigenvector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the comparison is proportional to C, placing the added density on a lambda eigenvector attains the lower bound. The spectral calculation follows the shared eigenvector along the affine reference path.

**Theorem 1.3 (A small loss restricts the positive reference floor).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.not_floor_of_log_increment_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.not_floor_of_log_increment_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The function lambda times log(1 + e/lambda) increases strictly for positive e. An observed loss at or below the bound for a given floor excludes every larger floor. This gives the spectral estimate used to compare compression of the positive-likelihood classes against the loss incurred by the zero class.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.log_increment_eq_of_eigenvector`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.log_increment_ge`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.not_floor_of_log_increment_le`
- Dependency: [D5/S3/Divergence/AudenaertBinaryHolevoBound](../../Divergence/AudenaertBinaryHolevoBound.md)

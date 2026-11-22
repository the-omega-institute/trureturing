# The trace-log cost of a reference increment

## Abstract

A sharp spectral lower bound for the trace-log pairing of a positive reference increment.

**Theorem 1.1 (Lower bound from a positive reference floor).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.log_increment_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.log_increment_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Koenraad M. R. Audenaert (2014). *Quantum Skew Divergence*. DOI: [10.1063/1.4901039](https://doi.org/10.1063/1.4901039). URL: <https://arxiv.org/abs/1304.5935v2>.

*Commentary.*

Assume u > 0, λ > 0, e ≥ 0, A ≥ uC, and C ≥ λI in the Löwner order. Let ρ be positive semidefinite with trace one. The unnormalized real trace pairing Re Tr[A(log(C + eρ) − log C)] is at least uλ log(1 + e/λ). The reference C can have arbitrary trace subject to these hypotheses, and C + eρ has trace Tr C + e. The decrease in relative entropy with the unequal-trace correction equals this pairing minus e. The proof uses Audenaert's derivative along the affine reference path and operator monotonicity of the matrix logarithm after pairing with a positive weight.

**Theorem 1.2 (Attainment at a unit eigenvector at the floor).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.log_increment_eq_of_eigenvector`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.log_increment_eq_of_eigenvector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume λ > 0, C ≥ λI and e ≥ 0. If v†v = 1 and Cv = λv, then ρ = vv† is positive semidefinite with trace one. For A = uC, the pairing equals uλ log(1 + e/λ) for every real u, attaining the lower bound when u > 0.

**Theorem 1.3 (A small loss restricts the positive reference floor).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.not_floor_of_log_increment_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.not_floor_of_log_increment_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume u > 0, e > 0, A ≥ uC, and that ρ is positive semidefinite with trace one. For a threshold θ > 0, a pairing at most uθ log(1 + e/θ) rules out C ≥ λI for every λ > θ, since λ log(1 + e/λ) increases strictly on λ > 0. In an application with likelihood classes, eρ can represent reference mass added for a zero-likelihood class. The estimate controls the trace-log cost of that addition when comparing it with compression of the positive-likelihood classes.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.log_increment_eq_of_eigenvector`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.log_increment_ge`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.not_floor_of_log_increment_le`
- Dependency: [D5/S3/Divergence/AudenaertBinaryHolevoBound](../../Divergence/AudenaertBinaryHolevoBound.md)

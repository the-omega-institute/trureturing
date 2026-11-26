# Singular weighted logarithm increment

## Abstract

A singular weighted logarithm increment is nonnegative and detects overlap exactly.

**Theorem 1.1 (Exact equality for the supported logarithm increment).**

Lean statement: `D5/S3/Quantum/Divergence/SingularWeightedLogIncrement.weighted_log_increment_nonneg_and_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/SingularWeightedLogIncrement.weighted_log_increment_nonneg_and_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Koenraad M. R. Audenaert (2014). *Quantum Skew Divergence*. DOI: [10.1063/1.4901039](https://doi.org/10.1063/1.4901039). URL: <https://arxiv.org/abs/1304.5935v2>.

*Acknowledgement.* Fumio Hiai (2024). *Log-majorization and matrix norm inequalities with application to quantum information*. DOI: [10.1007/s44146-024-00142-w](https://doi.org/10.1007/s44146-024-00142-w). URL: <https://arxiv.org/abs/2402.16067>.

*Commentary.*

Let C and rho be positive semidefinite matrices on Fin n. Let 0 < u ≤ v and e > 0, and suppose u times C ≤ A ≤ v times C. The real trace of A times the difference of log(C + e times rho) and log(C) is nonnegative. It is zero exactly when C times rho is zero.

Both endpoints are shifted by a positive multiple of the identity. Audenaert's resolvent representation expresses the shifted gap as the integral of a weighted inverse difference. The sandwich bounds each integrand by scalar multiples of the pairing with C. Inverse order and cancellation characterize its zero set. The integral over shifts greater than one gives a positive lower bound whenever there is overlap.

The upper sandwich places the weight on the support of each endpoint. The supported cross-log limit from AlphaZAffine and UmegakiSupportedNoise therefore yields convergence to the two CFC logarithms, with value zero on each kernel. The fixed lower bound survives this limit.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/SingularWeightedLogIncrement.weighted_log_increment_nonneg_and_eq_zero_iff`
- Dependency: [D5/S3/Divergence/AudenaertBinaryHolevoBound](../../Divergence/AudenaertBinaryHolevoBound.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiSupportedNoise](UmegakiSupportedNoise.md)
- Dependency: [D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity](../Measurements/FiniteMemoryHistoryCapacity.md)
- Dependency: [D5/S3/Quantum/Tomography/PurityPythagorasDecomposition](../Tomography/PurityPythagorasDecomposition.md)

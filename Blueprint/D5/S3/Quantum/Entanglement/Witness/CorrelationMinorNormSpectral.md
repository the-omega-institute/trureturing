# Actual native singular-value and nuclear tail correspondences

## Abstract

Actual native singular-value and nuclear tail correspondences

**Theorem 1.1 (gram toEuclideanLin).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.gram_toEuclideanLin`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.gram_toEuclideanLin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The actual real column Gram matrix acts as the adjoint composite of the Euclidean linear map of the original rectangular matrix.

**Theorem 1.2 (native singular value).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.native_singular_value`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.native_singular_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every real rectangular matrix, its native descending zero-extended singular values are exactly the square roots of the sorted column-Gram eigenvalues, with explicit finite index correspondence.

**Theorem 1.3 (traceNorm eq native sum).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.traceNorm_eq_native_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.traceNorm_eq_native_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The existing actual real rectangular CFC trace norm equals the complete native descending singular-value sum through the column dimension, retaining zero values.

**Theorem 1.4 (opNorm eq native first).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.opNorm_eq_native_first`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.opNorm_eq_native_first` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The actual induced Euclidean matrix operator norm equals the first native descending singular value. Zero maps and empty dimensions are included.

**Theorem 1.5 (traceNorm sub rankOne tail).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.traceNorm_sub_rankOne_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.traceNorm_sub_rankOne_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every real rectangular A and arbitrary actual Euclidean a,b, traceNorm(A)-operatorNorm(A) is at most traceNorm(A-ab transpose). An actual contractive projected dual witness proves this; zero a or b and rank deficiency remain included.

**Theorem 1.6 (native tail le centered).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.native_tail_le_centered`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.native_tail_le_centered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every retained length 1≤k≤n, the actual descending native singular-value tail from index one through k-1 is at most the actual CFC trace norm after subtracting ab transpose. Index one corresponds to the source one-based second singular value. This supplier is consumed by the actual marginal/purity theorem in CorrelationMinorNormCovariance.

**Theorem 1.7 (traceNorm transpose).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.traceNorm_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.traceNorm_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Transposition preserves the existing real rectangular CFC nuclear norm. The proof uses its actual attained contractive duality, including zero and rectangular cases.

**Theorem 1.8 (native tail eq traceNorm sub).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.native_tail_eq_traceNorm_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.native_tail_eq_traceNorm_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For positive finite row and column dimensions, the actual descending tail through the smaller dimension equals the CFC nuclear norm minus the Euclidean operator norm. All additional ambient singular values are proved zero by range dimension, rather than discarded by convention.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.gram_toEuclideanLin`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.native_singular_value`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.native_tail_eq_traceNorm_sub`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.native_tail_le_centered`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.opNorm_eq_native_first`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.traceNorm_eq_native_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.traceNorm_sub_rankOne_tail`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral.traceNorm_transpose`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry](CorrelationMinorNormGeometry.md)

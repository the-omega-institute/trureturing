# Actual normalized separable covariance nuclear bound

## Abstract

Actual normalized separable covariance nuclear bound

**Theorem 1.1 (weighted centered nuclear).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance.weighted_centered_nuclear`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance.weighted_centered_nuclear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For arbitrary finite real Euclidean families of local squared norm at most one and nonnegative weights summing to one, the actual centered weighted-outer CFC nuclear norm is bounded by sqrt((1-norm(mean x)^2)(1-norm(mean y)^2)). Zero weights and centered vectors are included. This is the covariance estimate attributed to Zhang2008 and Gittsovich2008, not a new covariance theorem.

**Theorem 1.2 (actual covariance nuclear).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance.actual_covariance_nuclear`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance.actual_covariance_nuclear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every actual separable complex state and complete trace-product-normalized local Hermitian bases, the actual covariance C-ab transpose uses precisely the coefficient means of the actual partial traces. Left retains Bob and Right Alice. The proof uses an arbitrary finite separable decomposition and actual Parseval/purity bounds. The spectral-tail/purity and actual D31 equality consumer are proved below in this same module.

**Theorem 1.3 (correlation tail purity).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance.correlation_tail_purity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance.correlation_tail_purity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For arbitrary positive finite dimensions and every actual separable state, the actual descending singular tail through min(dA,dB) squared is bounded by sqrt((1-Tr(rhoA squared))(1-Tr(rhoB squared))). Coefficient means are the actual partial traces and Parseval supplies their actual purities. Dimension one and empty tails are included.

**Theorem 1.4 (correlation tail corrected).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance.correlation_tail_corrected`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance.correlation_tail_corrected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The purity upper bound is at most sqrt(((d-1)/d)((D-1)/D)), d=min(dA,dB), D=max(dA,dB), in arbitrary positive finite dimensions. This corrects the missing square root in printed D31, without validating Appendix D.5 extra maximization assumptions. Covariance credit remains Zhang et al. (2008), Theorem 1, and Gittsovich et al. (2008), Proposition IV.2.

**Theorem 1.5 (d31 counterexample and equality).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance.d31_counterexample_and_equality`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance.d31_counterexample_and_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The actual separable density omega(4,0) has both maximally mixed marginals, hence FNF. In every normalized complete Bob basis with normalized Pauli Alice basis, its complete singular tail is exactly sqrt(3/8), equal to the purity and dimension corrections and strictly larger than printed D31 value 3/8. This is an exact matrix and spectral proof, not a finite control.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance.actual_covariance_nuclear`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance.correlation_tail_corrected`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance.correlation_tail_purity`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance.d31_counterexample_and_equality`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance.weighted_centered_nuclear`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral](CorrelationMinorNormSpectral.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron](CorrelationMinorNormTetrahedron.md)

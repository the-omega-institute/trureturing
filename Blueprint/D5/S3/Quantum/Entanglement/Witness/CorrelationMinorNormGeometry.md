# Actual normalized Hermitian correlation geometry

## Abstract

Actual normalized Hermitian correlation geometry

**Theorem 1.1 (Real trace pairings).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.hermitian_pair_real`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.hermitian_pair_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The complex trace of the product of two actual Hermitian matrices equals the complex inclusion of its real part. This directly reuses the existing HermitianMat trace inner product.

**Definition 1.2 (Actual real Hermitian coordinates).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.coordinates`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Coordinates are the real trace pairings with the given local Hermitian observables, valued in the existing real EuclideanSpace. No new density or norm structure is introduced.

**Theorem 1.3 (Completeness and reconstruction).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.coordinate_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.coordinate_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Every Hermitian n-by-n complex matrix is reconstructed as the sum of its real normalized coordinates times the n² basis matrices. The trace-dual family is proved complex-linearly independent and hence a complete matrix basis. Empty dimension remains included.

**Theorem 1.4 (Exact Parseval pairing).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.coordinates_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.coordinates_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For a complete trace-product-normalized Hermitian basis, the real Euclidean inner product of actual coordinate vectors is Re Tr(MN), for any Hermitian M and N. There is no factor of two.

**Theorem 1.5 (Purity is coordinate energy).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.coordinates_purity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.coordinates_purity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The squared coordinate norm is Re Tr(M²), with no FNF or purity assumption on the actual Hermitian matrix.

**Theorem 1.6 (Arbitrary-dimensional local purity).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.density_purity_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.density_purity_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Every actual positive-semidefinite trace-one complex matrix has purity between zero and one. The existing HermitianMat positivity/trace inequality supplies the arbitrary-dimensional upper bound; a qubit-only estimate is not substituted.

**Theorem 1.7 (The dimension lower bound).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.density_purity_dimension_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.density_purity_dimension_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

In every positive finite dimension n, an actual density matrix has purity at least 1/n. This is trace Cauchy–Schwarz against the actual identity.

**Theorem 1.8 (Actual product correlations).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.corr_product_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.corr_product_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The correlation trace of an actual tensor product of two Hermitian matrices equals the product of their actual real local coordinate entries.

**Theorem 1.9 (Any finite product decomposition).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.correlation_finite_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.correlation_finite_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For arbitrary finite real weights and actual Hermitian local factors, the correlation of the tensor-product sum equals the weighted sum of their actual coordinate outer products. This does not bound or reduce decomposition cardinality.

**Definition 1.10 (The sole full-order row).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.fullRows`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.fullRows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The row subset at order n in n rows is the full finite index set, with its inherited increasing order.

**Theorem 1.11 (Increasing Cauchy–Binet).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.full_order_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.full_order_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every real n-by-m matrix, the sum of squares of all increasing full-row minors is det(CCᵀ). The proof reuses the existing generic rectangular Cauchy–Binet body with natural increasing Fin order; rank deficiency and empty column-subset types are included.

**Theorem 1.12 (All full-order Schatten norms).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.full_order_norms`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.full_order_norms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every real n-by-m matrix, the actual increasing-compound Euclidean operator norm and every finite real Schatten-p norm for p≥1 equal sqrt(det(CCᵀ)). The existing single-row real/complex Gram and rectangular CFC Schatten proofs are consumed. Zero singular values and zero determinants remain included.

**Theorem 1.13 (Absolute determinant).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.square_full_order_norms`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.square_full_order_norms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every real square matrix the full-order infinity and finite p≥1 quantities equal abs(det C). No signed determinant is used as a norm.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.coordinate_reconstruction`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.coordinates`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.coordinates_inner`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.coordinates_purity`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.corr_product_entry`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.correlation_finite_decomposition`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.density_purity_bounds`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.density_purity_dimension_lower`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.fullRows`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.full_order_energy`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.full_order_norms`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.hermitian_pair_real`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry.square_full_order_norms`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation](CorrelationMinorNormFNFRefutation.md)
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../../Information/ActualPureQubitGeometry.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity](../../QuantumChannels/NuclearNormAdditivity.md)

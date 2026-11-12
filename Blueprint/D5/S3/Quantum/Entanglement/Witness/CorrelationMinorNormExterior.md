# Actual exterior-order and real-complex norm correspondences

## Abstract

Actual exterior-order and real-complex norm correspondences

**Theorem 1.1 (opNorm ofReal).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior.opNorm_ofReal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior.opNorm_ofReal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Real complexification preserves the actual rectangular Euclidean operator norm, including zero maps and empty finite index types.

**Theorem 1.2 (sorted singularValues ofReal).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior.sorted_singularValues_ofReal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior.sorted_singularValues_ofReal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For square real matrices the existing complex sorted singular values coincide with native real descending singular values, preserving multiplicity, zero spectrum and column-Gram normalization.

**Theorem 1.3 (complex opNorm sorted).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior.complex_opNorm_sorted`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior.complex_opNorm_sorted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The existing complex square SVD identifies the actual operator norm with the largest sorted singular value for every nonempty finite index type.

**Theorem 1.4 (compound order correspondence).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior.compound_order_correspondence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior.compound_order_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The actual natural increasing compound and the existing supplier compound differ exactly by diagonal sign unitaries from the finite order permutations. No sign, index or ordering convention is silently identified.

**Theorem 1.5 (cmnInf eq native product).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior.cmnInf_eq_native_product`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior.cmnInf_eq_native_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every real square matrix and every order h up to its size, the induced Euclidean norm of the natural increasing compound is the product of the largest h native descending singular values. This is consumed by the actual equal-dimensional CCNR proof; it is not an entrywise maximum.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior.cmnInf_eq_native_product`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior.complex_opNorm_sorted`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior.compound_order_correspondence`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior.opNorm_ofReal`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior.sorted_singularValues_ofReal`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral](CorrelationMinorNormSpectral.md)
- Dependency: [D5/S3/Quantum/Schatten/SingularValueOrder](../../Schatten/SingularValueOrder.md)
- Dependency: [D5/S3/SpectralTopology/RectangularDilation](../../../SpectralTopology/RectangularDilation.md)

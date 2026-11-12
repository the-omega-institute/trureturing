# Equal-dimensional CCNR specialization without filter normal form

## Abstract

Equal-dimensional CCNR specialization without filter normal form

**Theorem 1.1 (normalized identity singular lower).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCCNR.normalized_identity_singular_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCCNR.normalized_identity_singular_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every positive equal local dimension and actual complex trace-one density, normalized identities have unit Hermitian-coordinate norms in every pair of complete trace-product-normalized local bases. Their actual correlation pairing is 1/d, proving the largest native singular value is at least 1/d. This is the normalized application of Li, Poon and Sze (2011), Lemma 2.1; separability and FNF are not premises.

**Theorem 1.2 (equal dimensional ccnr).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCCNR.equal_dimensional_ccnr`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCCNR.equal_dimensional_ccnr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every integer d at least two and d <= h <= d squared, every actual density satisfying CCNR (the complete descending correlation singular-value sum is at most one) obeys M(h,infinity) <= (1/d)*((d-1)/(d*(h-1)))^(h-1), exactly the original B(d,d,h). The proof uses the actual compound product correspondence, AM-GM on the remaining h-1 singular values and monotonicity on the full real interval [1/d,1]. Potentially entangled CCNR states are included. No hidden separability or FNF restriction is introduced.

**Theorem 1.3 (equal dimensional ccnr full).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCCNR.equal_dimensional_ccnr_full`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCCNR.equal_dimensional_ccnr_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

At full smaller-side order h=d squared the increasing compound has one row, so the same bound holds for every actual finite Schatten p >= 1 and infinity, including rank-deficient states. Intermediate finite p, h<d, and unequal general dimensions remain outside this conclusion. In the stated operator range this criterion detects no entanglement beyond CCNR. The corresponding equal-dimensional p=1 comparison is already Li, Poon and Sze (2011), Theorem 2.4.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCCNR.equal_dimensional_ccnr`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCCNR.equal_dimensional_ccnr_full`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCCNR.normalized_identity_singular_lower`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior](CorrelationMinorNormExterior.md)

# Actual tetrahedral correlation-minor violations and attainment

## Abstract

Actual tetrahedral correlation-minor violations and attainment

**Definition 1.1 (tetraVector).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetraVector`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetraVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The four unit Bloch vectors are (+++), (+--), (-+-), (--+) divided by sqrt(3).

**Definition 1.2 (tetraProjector).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetraProjector`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetraProjector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Actual complex qubit matrices (I+v dot sigma)/2 are built with the existing Bloch reconstruction. Alice coordinate order is I,Z,X,Y divided by sqrt(2); this only permutes the traceless coordinates.

**Theorem 1.3 (tetra projector).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_projector`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_projector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Each of the four actual matrices is PSD, trace one and idempotent.

**Theorem 1.4 (tetra sum).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The sum of the four actual qubit projectors is twice the identity.

**Definition 1.5 (tetraFlag).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetraFlag`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetraFlag` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The four Bob factors are actual diagonal matrix units, embedded into every D≥4.

**Definition 1.6 (omega).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The actual state is (1-t)/4 times the sum of the four projector/flag products, plus t/(2D) times the ambient identity. This is not a scalar replacement for a state.

**Theorem 1.7 (omega separable).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_separable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_separable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For D≥4 and every real t in [0,1], an explicit normalized five-term decomposition proves separability using four product densities and the maximally mixed product density.

**Definition 1.8 (rowSlice).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.rowSlice`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.rowSlice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Actual Bob Hermitian operators have normalized coordinates equal to the correlation rows.

**Theorem 1.9 (omega correlation rows).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_correlation_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_correlation_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The actual correlation rows are the real trace coordinates of the Bob slices, in every complete trace-product-normalized Bob basis.

**Theorem 1.10 (omega gram entry).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_gram_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_gram_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Hermitian Parseval gives each row-Gram entry as the trace pairing of the actual row slices.

**Definition 1.11 (q0).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.q0`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.q0` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The identity-row Gram coefficient is (1-t)^2/8+(2t-t^2)/(2D).

**Definition 1.12 (q1).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.q1`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.q1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

All three traceless-row Gram coefficients are (1-t)^2/24.

**Theorem 1.13 (omega gram).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The actual row Gram is exactly diag(q0,q1,q1,q1), without any finite noise discretization.

**Theorem 1.14 (omega density).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_density`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The actual matrices are PSD and trace one throughout the full convex noise interval.

**Theorem 1.15 (omega noise).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_noise`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_noise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The state minus t I/(2D) is PSD. Every t>0 in the noise interval gives a positive definite state.

**Theorem 1.16 (omega marginals).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_marginals`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Right retains Alice and is exactly I2/2. Left retains Bob and is (1-t)/4 times the four occupied flags plus t ID/D.

**Theorem 1.17 (omega not fnf).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_not_fnf`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_not_fnf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every D≥5 and t<1, the unoccupied flag at index four proves that Bob is not maximally mixed. Thus the state is not in FNF.

**Theorem 1.18 (omega full norms).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_full_norms`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_full_norms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

In arbitrary complete normalized local Hermitian bases, every actual finite Schatten p≥1 and infinity full-order quantity equals sqrt(q0*q1^3). The natural increasing compound and zero cases are retained.

**Definition 1.19 (fourthThresholdSquared).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.fourthThresholdSquared`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.fourthThresholdSquared` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The common fourth-order proposed squared threshold is (D-1)^3/(11664 D^4).

**Definition 1.20 (fourthThreshold).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.fourthThreshold`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.fourthThreshold` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The original normalized alpha beta^3 expression is 1/sqrt(2D) times sqrt((D-1)/(18D)) cubed. It is also the full qubit-side fourth elementary symmetric polynomial.

**Theorem 1.21 (fourthThreshold sq).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.fourthThreshold_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.fourthThreshold_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The alpha beta^3 expression has exactly the displayed squared threshold for every D≥2.

**Theorem 1.22 (tetra energy lower).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_energy_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_energy_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every D≥4 and real t in [0,1], the actual squared full-order norm is at least (1-t)^8/110592.

**Theorem 1.23 (tetra uniform violation).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_uniform_violation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_uniform_violation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Every real t in [0,1/1000] and every integer 5≤D≤8 gives a strictly positive energy exceeding the proposed threshold. The dimension split is finite, while the noise proof covers its entire real interval.

**Theorem 1.24 (tetrahedral family).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetrahedral_family`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetrahedral_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Actual separable density states, non-FNF marginals, both original dimension conditions 2D≤16 and D≤8, and strict violation in every finite p≥1 and infinity are proved together. The theorem directly binds the operator comparison to bound(2,D,4) and the p=1 comparison to the actual fourth elementary symmetric sum over four normalized alpha/beta variables. It also retains the uniform squared margin: every norm squared is at least (4185/4096) times the proposed squared threshold. These refute only the no-FNF extensions, not the original FNF theorems.

**Theorem 1.25 (tetra attainment).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every D≥4 the actual zero-noise tetrahedral state has every full-order Schatten norm exactly 1/(192 sqrt(3)), in arbitrary normalized local bases.

**Theorem 1.26 (fourthThreshold eq bound).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.fourthThreshold_eq_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.fourthThreshold_eq_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The threshold is exactly the repository original Theorem 3 bound(2,D,4). The original parameter and exponent conventions are retained.

**Theorem 1.27 (tetra rank one).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_rank_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_rank_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The four PSD trace-one idempotent qubit projectors have actual matrix rank one. No design-existence assumption supplies this fact.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.fourthThreshold`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.fourthThresholdSquared`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.fourthThreshold_eq_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.fourthThreshold_sq`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_correlation_rows`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_density`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_full_norms`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_gram`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_gram_entry`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_marginals`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_noise`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_not_fnf`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.omega_separable`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.q0`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.q1`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.rowSlice`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetraFlag`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetraProjector`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetraVector`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_energy_lower`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_projector`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_rank_one`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetra_uniform_violation`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.tetrahedral_family`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry](CorrelationMinorNormGeometry.md)

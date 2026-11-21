# Evaluation at the projection boundary

## Abstract

The unsmoothed three-qubit witness has geodesic relative entropy log 2 against its faithful reference for every 0 < t ≤ 1.

**Theorem 1.1 (Spectral evaluation with a whitened projection).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicBoundary.geodesicRelativeEntropy_of_whitened_projection`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicBoundary.geodesicRelativeEntropy_of_whitened_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

When the first matrix is a positive multiple of a Hermitian projection and whitening gives twice a Hermitian projection Q, the proof uses the stipulated square-root and inverse identities to express the entropy as 2 log 2 times the real trace of the reference times Q. At t = 1 the left spectral factor is the identity.

**Theorem 1.2 (Exact log 2 boundary value).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicBoundary.geodesicRelativeEntropy_RMatrix_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicBoundary.geodesicRelativeEntropy_RMatrix_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Acknowledgement.* Andreas Bluhm; Ángela Capel; Paul Gondolf; Antonio Pérez-Hernández (2023). *Continuity of Quantum Entropic Quantities via Almost Convexity*. DOI: [10.1109/TIT.2023.3277892](https://doi.org/10.1109/TIT.2023.3277892). URL: <https://arxiv.org/pdf/2208.00922v3#page=27>.

*Commentary.*

The unsmoothed matrix is one quarter of a projection. Whitening by the faithful S_u gives I + X_A Z_B Z_C, twice a projection with reference weight one half. The resulting value is log 2 for 0 < u < 1/2 and 0 < t ≤ 1. Lemma 10.14, equation (593), gives the earlier rank-one block mechanism. Proposition 6.7 supplies the Belavkin–Staszewski conditional-entropy antecedent.

## References

- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicBoundary.geodesicRelativeEntropy_RMatrix_zero`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicBoundary.geodesicRelativeEntropy_of_whitened_projection`
- Dependency: [D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity](CapelCostaRicoForwardGeodesicDensity.md)
- Dependency: [D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular](CapelCostaRicoGeodesicModular.md)

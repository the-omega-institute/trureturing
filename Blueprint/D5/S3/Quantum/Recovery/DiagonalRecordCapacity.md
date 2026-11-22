# Quantum memory for a finite diagonal experiment

## Abstract

The distinct likelihood vectors give the exact quantum memory dimension of a diagonal experiment.

The experiment consists of a reference probability law on a finite basis and a family of comparison laws supported on it. At each positive reference coordinate, record the vector of comparison weights divided by the reference weight. The count is finite even when the comparison family is indexed by an infinite type. The two-state likelihood decomposition appears in Galke, van Luijk and Wilming, Appendix B. Kato's equation (62) gives the equivalent posterior count for classical bipartite experiments.

**Theorem 1.1 (Exact dimension for common physical recovery).**

Lean statement: `D5/S3/Quantum/Recovery/DiagonalRecordCapacity.sharp_recovery_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/DiagonalRecordCapacity.sharp_recovery_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Niklas Galke, Lauritz van Luijk, and Henrik Wilming (2024). *Sufficiency of Rényi Divergences*. DOI: [10.1109/TIT.2024.3376395](https://doi.org/10.1109/TIT.2024.3376395). URL: <https://arxiv.org/abs/2304.12989>.

*Acknowledgement.* Kohtaro Kato (2025). *Exact and Local Compression of Quantum Bipartite States*. DOI: [10.1109/TIT.2025.3562884](https://doi.org/10.1109/TIT.2025.3562884). URL: <https://arxiv.org/abs/2309.07434>.

*Acknowledgement.* Masato Koashi and Nobuyuki Imoto (2002). *Operations that do not disturb partially known quantum states*. URL: <https://arxiv.org/abs/quant-ph/0101144>.

*Commentary.*

Measure in the diagonal basis after decoding. The resulting stochastic kernel fixes the reference and every comparison law. Expanding the reference-weighted squared change in one likelihood ratio gives zero, so a positive transition stays inside the same likelihood class. Pulling the class measurement back through the decoder gives a perfect class measurement on the memory. The finite quantum measurement capacity theorem bounds the number of classes by the memory dimension. Recording the class in an orthogonal basis and preparing the reference law conditional on that class gives physical channels attaining the bound.

**Theorem 1.2 (Exact dimension for fixed-reference entropy preservation).**

Lean statement: `D5/S3/Quantum/Recovery/DiagonalRecordCapacity.sharp_entropy_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/DiagonalRecordCapacity.sharp_entropy_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Niklas Galke, Lauritz van Luijk, and Henrik Wilming (2024). *Sufficiency of Rényi Divergences*. DOI: [10.1109/TIT.2024.3376395](https://doi.org/10.1109/TIT.2024.3376395). URL: <https://arxiv.org/abs/2304.12989>.

*Acknowledgement.* Kohtaro Kato (2025). *Exact and Local Compression of Quantum Bipartite States*. DOI: [10.1109/TIT.2025.3562884](https://doi.org/10.1109/TIT.2025.3562884). URL: <https://arxiv.org/abs/2309.07434>.

*Commentary.*

The support-aware Petz equality theorem supplies one recovery channel constructed from the encoder and the reference. It recovers every comparison law whose Umegaki relative entropy is preserved. Conversely, applying data processing to the encoder and decoder gives equality for every comparison. The dimension bound and its attainment thus hold for arbitrary CPTP encoders.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/DiagonalRecordCapacity.sharp_entropy_dimension`
- Truth anchor: `D5/S3/Quantum/Recovery/DiagonalRecordCapacity.sharp_recovery_dimension`
- Dependency: [D5/S3/Quantum/Foundation/FinitePreparationChannel](../Foundation/FinitePreparationChannel.md)
- Dependency: [D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity](../Measurements/FiniteMemoryHistoryCapacity.md)
- Dependency: [D5/S3/Quantum/Recovery/CanonicalPetzEquality](CanonicalPetzEquality.md)
- Dependency: [D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation](../Subentropy/StrongSubadditivityRefutation.md)

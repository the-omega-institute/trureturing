# Spectral bounds for finite-memory discrimination

## Abstract

The leading spectrum of the discrimination dual limits decoding through a finite memory.

**Theorem 1.1 (Pure-state success is bounded by the leading dual eigenvalues).**

Lean statement: `D5/S3/Quantum/PureState/PhaseRecordSpectralMemory.pure_success_le_largestEigenvalueSum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseRecordSpectralMemory.pure_success_le_largestEigenvalueSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yonina C. Eldar, Alexandre Megretski, George C. Verghese (2003). *Designing optimal quantum detectors via semidefinite programming*. DOI: [10.1109/TIT.2003.809510](https://doi.org/10.1109/TIT.2003.809510). URL: <https://arxiv.org/abs/quant-ph/0205178>.

*Commentary.*

For normalized pure signals, any feasible discrimination dual bounds the score after a CPTP encoder into a memory of dimension M and an output POVM. Each pulled-back effect is compressed to a score-preserving rank-one effect bounded by the original effect. Their sum is a positive contraction of trace at most M. Pairing with the dual bounds the score by its largest M eigenvalues, with the sum cut off at the input dimension.

**Theorem 1.2 (The omitted phase amplitudes quantify lost guessing success).**

Lean statement: `D5/S3/Quantum/PureState/PhaseRecordSpectralMemory.phase_pGuess_spectral_tail_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseRecordSpectralMemory.phase_pGuess_spectral_tail_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite orthogonal phase ensemble with N labels and total amplitude S, the loss in optimal guessing after compression is at least S/N times the sum of the amplitudes omitted by selecting the largest M amplitudes. The theorem permits equal and zero amplitudes.

## References

- Truth anchor: `D5/S3/Quantum/PureState/PhaseRecordSpectralMemory.phase_pGuess_spectral_tail_gap`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseRecordSpectralMemory.pure_success_le_largestEigenvalueSum`
- Dependency: [D5/S3/Quantum/PureState/PhaseRecordMemory](PhaseRecordMemory.md)
